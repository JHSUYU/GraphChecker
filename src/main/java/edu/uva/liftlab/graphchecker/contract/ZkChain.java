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

public final class ZkChain {
    public static final String FILE = "zk_chain.jsonl";
    public static final String PATH = "ZK_CHAIN_PATH";
    public static final String OCCURRENCE = "ZK_CHAIN_OCCURRENCE";
    public static final String KEYS = "ZK_CHAIN_KEYS";
    public static final String CONTENT_KEYS = "contentKeys";
    public static final String EDGE = "ZK_EDGE";
    public static final String ENVIRONMENT = "CAUSYNTH_ZK_CHAIN";

    private final List<JsonObject> rows;
    private final Map<String, String> paths =
            new LinkedHashMap<String, String>();
    private final Set<String> occurrences = new LinkedHashSet<String>();
    private final Map<String, Set<String>> pointersOf =
            new LinkedHashMap<String, Set<String>>();
    private final Set<String> keyed = new LinkedHashSet<String>();

    private ZkChain(List<JsonObject> rows) {
        this.rows = rows;
        for (JsonObject row : rows) take(row);
    }

    public static ZkChain of(List<JsonObject> rows) {
        return new ZkChain(new ArrayList<JsonObject>(rows));
    }

    public static ZkChain read(Path file) throws IOException {
        return new ZkChain(file == null || !Files.isRegularFile(file)
                ? new ArrayList<JsonObject>() : RowCodec.readJsonl(file));
    }

    public static ZkChain held(Path file) throws IOException {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        String keys = "\"" + KEYS + "\"";
        RowCodec.eachLine(file, line -> {
            if (!line.contains(keys)) rows.add(RowCodec.fromLine(line));
            return true;
        });
        return new ZkChain(rows);
    }

    public boolean holdsPath(String transport, String slot) {
        return paths.containsKey(transport + "\n" + slot);
    }

    public boolean holds(String occurrence) {
        return occurrences.contains(occurrence);
    }

    public boolean empty() {
        return rows.isEmpty();
    }

    public ZkChain grown(List<JsonObject> growth) {
        ZkChain grown = new ZkChain(new ArrayList<JsonObject>(rows));
        for (JsonObject edge : growth) {
            if (!EDGE.equals(optionalString(edge, "kind"))) continue;
            String transport = optionalString(edge, "transport");
            String slot = optionalString(edge, "location");
            String occurrence = optionalString(edge, "occurrence");
            Set<String> pointers = new LinkedHashSet<String>();
            if (edge.has("pointers")) {
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

    public ZkChain rekeyed(List<JsonObject> keys) {
        List<JsonObject> kept = new ArrayList<JsonObject>();
        for (JsonObject row : rows) {
            if (!KEYS.equals(optionalString(row, "kind"))) kept.add(row);
        }
        kept.addAll(keys);
        return new ZkChain(kept);
    }

    public Map<String, Set<String>> pointers() {
        return Collections.unmodifiableMap(pointersOf);
    }

    public Set<String> paths() {
        return Collections.unmodifiableSet(paths.keySet());
    }

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
