package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * THE ZOOKEEPER CHAIN a plan keeps symbolic ({@code zk_chain.jsonl}, PIPELINE
 * §7.8, SYMBOL-SCOPE §6.4): the znodes the anchor's values rest on, every
 * occurrence on its backward chain over the store's (path, version) edges --
 * each writer of a chain path, each decoder, reader and callback the chain
 * reached ({@code causynth.ZkCausalGraph}) -- and, field by field, the leaf
 * pointers of a path each chain decode and writer holds ({@value #KEYS},
 * the plan rows' {@value #CONTENT_KEYS}).  One row each:
 * <pre>
 *   {"schemaVersion":1,"kind":"ZK_CHAIN_PATH","transport":"SOLR_ZK",
 *    "location":"&lt;the path as the trace spells it&gt;",
 *    "slot":"&lt;the path as a store row's location spells it&gt;"}
 *   {"schemaVersion":1,"kind":"ZK_CHAIN_OCCURRENCE",
 *    "occurrenceId":"&lt;rendered address&gt;"}
 *   {"schemaVersion":1,"kind":"ZK_CHAIN_KEYS","occurrenceId":"...",
 *    "location":"...","slot":"...","pointers":["&lt;prefix, | for /&gt;"]}
 * </pre>
 * PLAN writes the iteration's; each GROW generation writes its own, the one
 * before it with what its round's {@value #EDGE} rows named appended
 * ({@link #grown}): the chain grows, path by path and field by field, never
 * shrinks.
 */
public final class ZkChain {
    /** The chain beside a plan, and the iteration's link to the current. */
    public static final String FILE = "zk_chain.jsonl";
    public static final String PATH = "ZK_CHAIN_PATH";
    public static final String OCCURRENCE = "ZK_CHAIN_OCCURRENCE";
    public static final String KEYS = "ZK_CHAIN_KEYS";
    /** A plan row's leaf prefixes: {location, slot, pointer} each. */
    public static final String CONTENT_KEYS = "contentKeys";
    /** A growth row: a store edge a replay ran past the chain. */
    public static final String EDGE = "ZK_EDGE";

    private final List<JsonObject> rows;
    /** transport + "\n" + slot -> the trace's spelling, each chain path. */
    private final Map<String, String> paths =
            new LinkedHashMap<String, String>();
    private final Set<String> occurrences = new LinkedHashSet<String>();
    /** slot -> the pointers any chain occurrence holds of it. */
    private final Map<String, Set<String>> pointersOf =
            new LinkedHashMap<String, Set<String>>();
    /** occurrence + "\n" + slot of each keys row. */
    private final Set<String> keyed = new LinkedHashSet<String>();

    private ZkChain(List<JsonObject> rows) {
        this.rows = rows;
        for (JsonObject row : rows) take(row);
    }

    /** The chain these rows state (PLAN's, {@code causynth.ZkCausalGraph}). */
    public static ZkChain of(List<JsonObject> rows) {
        return new ZkChain(new ArrayList<JsonObject>(rows));
    }

    /** The chain a file states; none (no such file) is the empty one. */
    public static ZkChain read(Path file) throws IOException {
        return new ZkChain(file == null || !Files.isRegularFile(file)
                ? new ArrayList<JsonObject>() : RowCodec.readJsonl(file));
    }

    /** Whether the chain holds a store path, by its row spelling. */
    public boolean holdsPath(String transport, String slot) {
        return paths.containsKey(transport + "\n" + slot);
    }

    /** Whether an occurrence (its rendered address) is on the chain. */
    public boolean holds(String occurrence) {
        return occurrences.contains(occurrence);
    }

    public boolean empty() {
        return rows.isEmpty();
    }

    /**
     * This chain grown by each {@value #EDGE} row of {@code growth}: its
     * path and its occurrence where the chain holds them not yet, and the
     * occurrence's keys of the path where it states none -- the pointers
     * the chain holds of that path (what the anchor rests on there), else,
     * for a path new to the chain, those the edge's replay named at the
     * occurrence ({@code pointers}); none known, no keys row: the whole
     * document.
     */
    public ZkChain grown(List<JsonObject> growth) {
        ZkChain grown = new ZkChain(new ArrayList<JsonObject>(rows));
        for (JsonObject edge : growth) {
            if (!EDGE.equals(optionalString(edge, "kind"))) continue;
            String transport = optionalString(edge, "transport");
            String slot = optionalString(edge, "location");
            String occurrence = optionalString(edge, "occurrence");
            Set<String> pointers = new LinkedHashSet<String>(
                    grown.pointers(slot));
            if (pointers.isEmpty() && edge.has("pointers")) {
                for (JsonElement pointer
                        : edge.getAsJsonArray("pointers")) {
                    pointers.add(pointer.getAsString());
                }
            }
            if (!grown.holdsPath(transport, slot)) {
                JsonObject path = row(PATH);
                path.addProperty("transport", transport);
                path.addProperty("location", slot);
                path.addProperty("slot", slot);
                grown.add(path);
            }
            if (!grown.holds(occurrence)) {
                JsonObject held = row(OCCURRENCE);
                held.addProperty("occurrenceId", occurrence);
                grown.add(held);
            }
            if (!pointers.isEmpty()
                    && !grown.keyed.contains(occurrence + "\n" + slot)) {
                JsonObject keys = row(KEYS);
                keys.addProperty("occurrenceId", occurrence);
                keys.addProperty("location", grown.location(transport, slot));
                keys.addProperty("slot", slot);
                JsonArray stated = new JsonArray();
                for (String pointer : pointers) stated.add(pointer);
                keys.add("pointers", stated);
                grown.add(keys);
            }
        }
        return grown;
    }

    /**
     * This chain with its {@value #KEYS} rows replaced by {@code keys}: the
     * fields read off the seed replay's own composition ({@code
     * compose.ZkKeysMain}), exact where PLAN's were by leaf identity.
     */
    public ZkChain rekeyed(List<JsonObject> keys) {
        List<JsonObject> kept = new ArrayList<JsonObject>();
        for (JsonObject row : rows) {
            if (!KEYS.equals(optionalString(row, "kind"))) kept.add(row);
        }
        kept.addAll(keys);
        return new ZkChain(kept);
    }

    /** Each slot's pointers, over every keys row. */
    public Map<String, Set<String>> pointers() {
        return Collections.unmodifiableMap(pointersOf);
    }

    /** The chain's paths: transport + "\n" + slot each. */
    public Set<String> paths() {
        return Collections.unmodifiableSet(paths.keySet());
    }

    /** An occurrence's plan-row keys, {location, slot, pointer} each, in
     *  chain order; empty where it holds none. */
    public JsonArray contentKeys(String occurrence) {
        JsonArray keys = new JsonArray();
        for (JsonObject row : rows) {
            if (!KEYS.equals(optionalString(row, "kind"))
                    || !occurrence.equals(optionalString(row,
                    "occurrenceId"))) {
                continue;
            }
            for (JsonElement pointer : row.getAsJsonArray("pointers")) {
                JsonObject key = new JsonObject();
                key.addProperty("location", optionalString(row, "location"));
                key.addProperty("slot", optionalString(row, "slot"));
                key.addProperty("pointer", pointer.getAsString());
                keys.add(key);
            }
        }
        return keys;
    }

    public List<JsonObject> rows() {
        return Collections.unmodifiableList(rows);
    }

    public void write(Path file) throws IOException {
        RowCodec.writeJsonl(file, rows);
    }

    private Set<String> pointers(String slot) {
        Set<String> held = pointersOf.get(slot);
        return held == null ? Collections.<String>emptySet() : held;
    }

    /** The trace's spelling of a chain path, else its slot's. */
    private String location(String transport, String slot) {
        String location = paths.get(transport + "\n" + slot);
        return location == null || location.isEmpty() ? slot : location;
    }

    private void add(JsonObject row) {
        rows.add(row);
        take(row);
    }

    private void take(JsonObject row) {
        String kind = optionalString(row, "kind");
        if (PATH.equals(kind)) {
            paths.put(optionalString(row, "transport") + "\n"
                    + optionalString(row, "slot"),
                    optionalString(row, "location"));
        } else if (OCCURRENCE.equals(kind)) {
            occurrences.add(optionalString(row, "occurrenceId"));
        } else if (KEYS.equals(kind)) {
            String slot = optionalString(row, "slot");
            keyed.add(optionalString(row, "occurrenceId") + "\n" + slot);
            Set<String> held = pointersOf.computeIfAbsent(slot,
                    ignored -> new LinkedHashSet<String>());
            if (row.has("pointers")) {
                for (JsonElement pointer : row.getAsJsonArray("pointers")) {
                    held.add(pointer.getAsString());
                }
            }
        }
    }

    private static JsonObject row(String kind) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", kind);
        return row;
    }
}
