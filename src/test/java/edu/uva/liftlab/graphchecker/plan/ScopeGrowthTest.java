package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;

/**
 * SYMBOL-SCOPE section 2: the scope grows where the slice stops at it --
 * toward a callee's body, a field's owner and writers, a writer's callers,
 * nearest the throw first -- and never toward the target's own callers or a
 * clock.
 */
public class ScopeGrowthTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    interface Store {
        long get();
    }

    static final class Impl implements Store {
        private long value;

        @Override
        public long get() {
            return value;
        }
    }

    static class Base {
        public long get() {
            return System.nanoTime();
        }
    }

    static final class Inherits extends Base implements Store {
    }

    /** A constant body is no state to analyse. */
    static final class Fixed implements Store {
        @Override
        public long get() {
            return Long.MAX_VALUE;
        }
    }

    static final class Holder {
        static final Object CONSTANT = new Object();
        final long fixed = 1;
        long shared;

        void set(long value) {
            shared = value;
        }
    }

    static final class Writer {
        void write(Holder holder) {
            holder.shared = 1;
        }
    }

    static final class Setter {
        void write(Holder holder) {
            holder.set(2);
        }
    }

    private static final String T = ScopeGrowthTest.class.getName();
    private static final String GET = "<" + T + "$Store: long get()>";
    private static final String SHARED = "<" + T + "$Holder: long shared>";

    @Test
    public void theFrontierIsWhereTheSliceStopsNearestFirst() {
        String set = "<" + T + "$Holder: void set(long)>";
        List<Map<String, Object>> edges = Arrays.asList(
                edge("exception_throw", "m::$r9", "m#u9#exception:E", ""),
                edge("local_def_use", "m::$l3", "m::$r9", ""),
                edge("call_return", "<B: java.lang.String say()>.return",
                        "m::$l3", "<B: java.lang.String say()>"),
                edge("exception_guard", "m::$z0", "m#u9#exception:E", ""),
                edge("local_def_use", "m::$l1", "m::$z0", ""),
                edge("local_def_use", "<M: void m(long)>.param0:long",
                        "m::$l1", ""),
                edge("call_return", GET + ".return", "m::$l1", GET),
                edge("field_read", SHARED, "m::$z0", ""),
                edge("field_write", set + ".param0:long", SHARED, ""),
                edge("field_write", "<R: void readFields(java.io.DataInput)>"
                        + ".param0:java.io.DataInput", SHARED, ""),
                edge("call_return", "<C: long now()>.return", "m::$l1",
                        "<C: long now()>"),
                edge("call_return", "<A: long own()>.return", "m::$l1",
                        "<A: long own()>"),
                edge("field_write", "w::$l0", "<W: long far>", ""));
        List<String> found = new ArrayList<>();
        for (JsonObject row : ScopeFrontier.rows(edges,
                "<A: long own()>"::equals,
                Collections.singleton("<C: long now()>"),
                Collections.singleton("<M: void m(long)>"))) {
            found.add(row.get("kind").getAsString() + " "
                    + row.get("signature").getAsString() + " "
                    + row.get("distance").getAsInt());
        }
        assertEquals(Arrays.asList(
                "FIELD " + SHARED + " 1",
                "CALLEE " + GET + " 2",
                "FORMAL " + set + " 3",
                "ROOT <M: void m(long)> 0"), found);
    }

    /** A grown class holding a new root of the target's region is taken
     *  back, and never taken again. */
    @Test
    public void growthNeverMovesTheTargetsRoot() throws Exception {
        Path root = fixtures();
        Path scope = folder.newFolder().toPath();
        Path grown = folder.newFolder().toPath();
        String set = "FORMAL <" + T + "$Holder: void set(long)>";
        String moved = "<" + T + "$Setter: void write(" + T + "$Holder)>";
        assertEquals("1 added 1 class(es), 1 of 8 grown",
                grow(grown, scope, root, set, "<M: void m()>"));
        assertEquals("1 took back [" + T + "$Setter]: each held a new root "
                + "of the target's region", grow(grown, scope, root, set,
                "<M: void m()>", moved));
        assertEquals("0 added 0 class(es), 1 of 8 grown",
                grow(grown, scope, root, set, "<M: void m()>"));
    }

    private String grow(Path grown, Path scope, Path root, String row,
                        String... roots) throws Exception {
        StringBuilder frontier = new StringBuilder();
        String[] parts = row.split(" ", 2);
        frontier.append("{\"kind\":\"").append(parts[0])
                .append("\",\"signature\":\"").append(parts[1])
                .append("\",\"distance\":1}\n");
        for (String held : roots) {
            frontier.append("{\"kind\":\"ROOT\",\"signature\":\"")
                    .append(held).append("\",\"distance\":0}\n");
        }
        Path file = folder.newFile().toPath();
        Files.write(file, frontier.toString().getBytes("UTF-8"));
        java.io.ByteArrayOutputStream out = new java.io.ByteArrayOutputStream();
        java.io.PrintStream was = System.out;
        System.setOut(new java.io.PrintStream(out, true, "UTF-8"));
        try {
            ScopeGrowth.main(new String[]{grown.toString(), file.toString(),
                    "8", scope.toString(), root.toString()});
        } finally {
            System.setOut(was);
        }
        return out.toString("UTF-8").trim();
    }

    @Test
    public void aRowGrowsTowardBodiesOwnersAndWriters() throws Exception {
        ScopeGrowth growth = new ScopeGrowth();
        growth.scan(fixtures());
        Map<String, List<String>> expected = new LinkedHashMap<>();
        expected.put("CALLEE " + GET, names("Base", "Impl"));
        expected.put("CALLEE <" + T + "$Impl: long get()>", names("Impl"));
        expected.put("FIELD <" + T + "$Impl: long value>", names("Impl"));
        expected.put("FIELD " + SHARED, names("Holder", "Writer"));
        expected.put("FIELD <" + T + "$Holder: long fixed>", names("Holder"));
        expected.put("FIELD <" + T + "$Holder: java.lang.Object CONSTANT>",
                names());
        expected.put("FORMAL <" + T + "$Holder: void set(long)>",
                names("Setter"));
        expected.put("CALLEE <java.lang.Runnable: void run()>", names());
        expected.put("FIELD <java.lang.Thread: long tid>", names());
        for (Map.Entry<String, List<String>> row : expected.entrySet()) {
            String[] parts = row.getKey().split(" ", 2);
            assertEquals(row.getKey(), row.getValue(), new ArrayList<>(
                    growth.resolve(parts[0], parts[1])));
        }
    }

    /** A class root holding the fixtures' class files. */
    private Path fixtures() throws Exception {
        Path root = folder.newFolder().toPath();
        for (Class<?> fixture : Arrays.asList(Store.class, Impl.class,
                Base.class, Inherits.class, Fixed.class, Holder.class,
                Writer.class, Setter.class)) {
            String file = fixture.getName().replace('.', '/') + ".class";
            Path target = root.resolve(file);
            Files.createDirectories(target.getParent());
            try (InputStream in = fixture.getClassLoader()
                    .getResourceAsStream(file)) {
                Files.copy(in, target);
            }
        }
        return root;
    }

    private static List<String> names(String... simple) {
        TreeSet<String> names = new TreeSet<>();
        for (String name : simple) names.add(T + "$" + name);
        return new ArrayList<>(names);
    }

    private static Map<String, Object> edge(String kind, String from,
                                            String to, String invoke) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("kind", kind);
        edge.put("fromCell", from);
        edge.put("toCell", to);
        if (!invoke.isEmpty()) edge.put("invoke", invoke);
        return edge;
    }
}
