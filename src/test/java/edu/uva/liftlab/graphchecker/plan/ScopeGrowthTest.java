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
 * toward a callee's body and a field's owner and writers, nearest the throw
 * first -- and never toward a caller or a clock.
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

    static final class Holder {
        long shared;
        Object[] slots;
    }

    static final class Writer {
        void write(Holder holder) {
            holder.shared = 1;
        }
    }

    static final class Reader {
        Object read(Holder holder) {
            return holder.slots[0];
        }
    }

    private static final String T = ScopeGrowthTest.class.getName();
    private static final String GET = "<" + T + "$Store: long get()>";
    private static final String SHARED = "<" + T + "$Holder: long shared>";

    @Test
    public void theFrontierIsWhereTheSliceStopsNearestFirst() {
        List<Map<String, Object>> edges = Arrays.asList(
                edge("exception_throw", "m::$z0", "m#u9#exception:E", ""),
                edge("local_def_use", "m::$l1", "m::$z0", ""),
                edge("call_return", GET + ".return", "m::$l1", GET),
                edge("field_read", SHARED, "m::$z0", ""),
                edge("call_return", "<C: long now()>.return", "m::$l1",
                        "<C: long now()>"),
                edge("call_return", "<A: long own()>.return", "m::$l1",
                        "<A: long own()>"),
                edge("field_write", "w::$l0", "<W: long far>", ""));
        List<String> found = new ArrayList<>();
        for (JsonObject row : ScopeFrontier.rows(edges,
                "<A: long own()>"::equals,
                Collections.singleton("<C: long now()>"))) {
            found.add(row.get("kind").getAsString() + " "
                    + row.get("signature").getAsString() + " "
                    + row.get("distance").getAsInt());
        }
        assertEquals(Arrays.asList(
                "FIELD " + SHARED + " 1",
                "CALLEE " + GET + " 2",
                "FIELD <W: long far> " + Integer.MAX_VALUE), found);
    }

    @Test
    public void aRowGrowsTowardBodiesOwnersAndWriters() throws Exception {
        Path root = folder.newFolder().toPath();
        for (Class<?> fixture : Arrays.asList(Store.class, Impl.class,
                Holder.class, Writer.class, Reader.class)) {
            String file = fixture.getName().replace('.', '/') + ".class";
            Path target = root.resolve(file);
            Files.createDirectories(target.getParent());
            try (InputStream in = fixture.getClassLoader()
                    .getResourceAsStream(file)) {
                Files.copy(in, target);
            }
        }
        ScopeGrowth growth = new ScopeGrowth();
        growth.scan(root);
        Map<String, List<String>> expected = new LinkedHashMap<>();
        expected.put("CALLEE " + GET, names("Impl"));
        expected.put("CALLEE <" + T + "$Impl: long get()>", names("Impl"));
        expected.put("FIELD <" + T + "$Impl: long value>", names("Impl"));
        expected.put("FIELD " + SHARED, names("Holder", "Writer"));
        expected.put("FIELD <" + T + "$Holder: java.lang.Object[] slots>",
                names("Holder", "Reader"));
        expected.put("FIELD <java.lang.Thread: long tid>", names());
        for (Map.Entry<String, List<String>> row : expected.entrySet()) {
            String[] parts = row.getKey().split(" ", 2);
            assertEquals(row.getKey(), row.getValue(), new ArrayList<>(
                    growth.resolve(parts[0], parts[1])));
        }
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
