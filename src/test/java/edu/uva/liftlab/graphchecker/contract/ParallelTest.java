package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * Independent items on every core, their results in the items' order: what
 * is made of them is what one thread made of them in turn, byte for byte
 * (the planner's keys and rows, PIPELINE §7.9).
 */
public class ParallelTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    /** Results in the items' order however long each took; the first
     *  failure in the items' order is the one thrown. */
    @Test
    public void mapKeepsTheItemsOrder() throws IOException {
        List<Integer> items = new ArrayList<Integer>();
        for (int at = 0; at < 2000; at++) items.add(at);
        List<String> done = Parallel.map(items, item -> {
            if (item % 7 == 0) Thread.yield();
            return "#" + item;
        });
        for (int at = 0; at < items.size(); at++) {
            assertEquals("#" + at, done.get(at));
        }
        try {
            Parallel.map(items, item -> {
                if (item >= 5) throw new IOException("item " + item);
                return item;
            });
            fail("a failing item fails the map");
        } catch (IOException failed) {
            assertEquals("item 5", failed.getMessage());
        }
    }

    /** One key's items run on one thread in their order: what remembers
     *  its asking order among them sees one thread's order. */
    @Test
    public void groupedRunsOneKeyInOrderOnOneThread() throws IOException {
        List<String> items = new ArrayList<String>();
        for (int at = 0; at < 3000; at++) items.add("k" + (at % 37) + ":" + at);
        Map<String, List<Integer>> seen =
                new ConcurrentHashMap<String, List<Integer>>();
        Map<String, Thread> by = new ConcurrentHashMap<String, Thread>();
        List<String> done = Parallel.grouped(items, ParallelTest::key,
                item -> {
                    String key = key(item);
                    Thread was = by.putIfAbsent(key, Thread.currentThread());
                    assertTrue(was == null || was == Thread.currentThread());
                    seen.computeIfAbsent(key, any -> Collections
                            .synchronizedList(new ArrayList<Integer>()))
                            .add(Integer.parseInt(item.substring(
                                    item.indexOf(':') + 1)));
                    return item.toUpperCase();
                });
        for (int at = 0; at < items.size(); at++) {
            assertEquals(items.get(at).toUpperCase(), done.get(at));
        }
        for (List<Integer> order : seen.values()) {
            List<Integer> sorted = new ArrayList<Integer>(order);
            Collections.sort(sorted);
            assertEquals(sorted, order);
        }
    }

    private static String key(String item) {
        return item.substring(0, item.indexOf(':'));
    }

    /** A stream hands its results in the source's order; one item alone
     *  is computed on the calling thread. */
    @Test
    public void streamHandsResultsInOrder() throws IOException {
        int[] next = {0};
        List<Integer> taken = new ArrayList<Integer>();
        Parallel.stream(() -> next[0] < 500 ? next[0]++ : null,
                item -> item * 2, taken::add);
        for (int at = 0; at < 500; at++) {
            assertEquals(Integer.valueOf(2 * at), taken.get(at));
        }
        Thread caller = Thread.currentThread();
        boolean[] given = {false};
        Parallel.stream(() -> given[0] ? null : (given[0] = true),
                item -> {
                    assertTrue(Thread.currentThread() == caller);
                    return item;
                }, item -> { });
    }

    /** A file written and read by blocks of whole lines reads back as it
     *  was written, a line longer than a block, blank lines and CRLF
     *  endings included, and is the bytes a line-by-line writer writes. */
    @Test
    public void rowsReadAndWriteByBlocks() throws IOException {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        StringBuilder expected = new StringBuilder();
        StringBuilder wide = new StringBuilder();
        for (int at = 0; at < 300_000; at++) wide.append((char) ('a' + at % 26));
        for (int at = 0; at < 20_000; at++) {
            JsonObject row = new JsonObject();
            row.addProperty("n", at);
            row.addProperty("text", at == 777 ? wide.toString()
                    : "ré世-" + at);
            rows.add(row);
            expected.append(RowCodec.toLine(row)).append('\n');
        }
        Path file = folder.getRoot().toPath().resolve("rows.jsonl");
        RowCodec.writeAll(file, rows, row -> row);
        assertArrayEquals(expected.toString().getBytes(
                StandardCharsets.UTF_8), Files.readAllBytes(file));
        List<Integer> read = RowCodec.readAll(file,
                row -> row.get("n").getAsInt());
        assertEquals(rows.size(), read.size());
        for (int at = 0; at < read.size(); at++) {
            assertEquals(Integer.valueOf(at), read.get(at));
        }
        Path spaced = folder.getRoot().toPath().resolve("spaced.jsonl");
        Files.write(spaced, ("{\"n\":1}\r\n\r\n  \n{\"n\":2}\n{\"n\":3}")
                .getBytes(StandardCharsets.UTF_8));
        List<Integer> kept = new ArrayList<Integer>();
        RowCodec.readEach(spaced, row -> row.get("n").getAsInt(), kept::add);
        assertEquals(java.util.Arrays.asList(1, 2, 3), kept);
        assertEquals(Collections.emptyList(), RowCodec.readAll(
                folder.getRoot().toPath().resolve("absent.jsonl"),
                row -> row));
        try {
            RowCodec.readAll(spaced, row -> {
                throw new UncheckedIOException(new IOException(
                        "row " + row.get("n")));
            });
            fail("a row that does not read fails the read");
        } catch (UncheckedIOException failed) {
            assertEquals("row 1", failed.getCause().getMessage());
        }
    }
}
