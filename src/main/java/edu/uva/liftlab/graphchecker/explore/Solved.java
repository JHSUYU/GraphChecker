package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.Z3;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.FileSystemException;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

final class Solved {
    static final String DIR = "solved";
    static final Solved NONE = new Solved(null);

    private final Path dir;

    private Solved(Path dir) {
        this.dir = dir;
    }

    static Solved in(Path iteration) {
        return new Solved(iteration.resolve(DIR));
    }

    static Solved at(Path dir) {
        return dir == null ? NONE : new Solved(dir);
    }

    Path dir() {
        return dir;
    }

    static final class Key {
        final String sha256;
        final Map<String, String> names;

        Key(String sha256, Map<String, String> names) {
            this.sha256 = sha256;
            this.names = Collections.unmodifiableMap(
                    new LinkedHashMap<String, String>(names));
        }

        static Key of(String query) {
            SmtNames.Canonical canonical = SmtNames.canonical(query);
            return new Key(ArtifactIO.sha256(canonical.text),
                    canonical.names);
        }

        Key of(Collection<String> symbols) {
            Map<String, String> named = new LinkedHashMap<String, String>();
            for (String symbol : symbols) {
                String held = names.get(symbol);
                if (held != null) named.put(symbol, held);
            }
            return new Key(sha256, named);
        }
    }

    Z3.Answer answer(String query, Collection<String> modelSymbols,
                     Supplier<Z3.Answer> z3) throws IOException {
        return answer(Key.of(query), modelSymbols, z3);
    }

    Z3.Answer answer(Key key, Collection<String> modelSymbols,
                     Supplier<Z3.Answer> z3) throws IOException {
        Z3.Answer kept = kept(key);
        if (kept != null && whole(kept, modelSymbols)) {
            System.err.println("causynth: query " + key.sha256
                    + " answered " + kept.status() + " as kept in " + dir
                    + ": no z3 run");
            return kept;
        }
        Z3.Answer answer = z3.get();
        if (dir != null && whole(answer, modelSymbols)
                && namesNone(answer, key)) {
            try {
                keep(key, answer);
            } catch (IOException unwritten) {
                System.err.println("causynth: query " + key.sha256
                        + "'s answer not kept in " + dir + ": " + unwritten);
            }
        }
        return answer;
    }

    static boolean whole(Z3.Answer answer, Collection<String> modelSymbols) {
        if (answer.unsat()) return true;
        return answer.sat() && (modelSymbols == null
                || answer.values().keySet().containsAll(modelSymbols));
    }

    private static boolean namesNone(Z3.Answer answer, Key key) {
        Set<String> named = new HashSet<String>();
        for (String value : answer.values().values()) {
            SmtNames.symbols(value, named);
        }
        named.retainAll(key.names.keySet());
        return named.isEmpty();
    }

    private Z3.Answer kept(Key key) throws IOException {
        if (dir == null) return null;
        JsonObject json;
        try {
            json = ExploreCodec.readObject(dir.resolve(key.sha256 + ".json"));
        } catch (FileSystemException unread) {
            return null;
        }
        if (!key.sha256.equals(JsonFields.primitiveString(json, "key"))) {
            throw new IOException("the answer kept as " + key.sha256
                    + " in " + dir + " is of key "
                    + JsonFields.primitiveString(json, "key"));
        }
        Map<String, String> asker = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> name : key.names.entrySet()) {
            asker.put(name.getValue(), name.getKey());
        }
        String status = JsonFields.primitiveString(json, "status");
        Map<String, String> values = new LinkedHashMap<String, String>();
        for (Map.Entry<String, JsonElement> value
                : JsonFields.object(json, "values").entrySet()) {
            String symbol = asker.get(value.getKey());
            if (symbol != null) {
                values.put(symbol, value.getValue().getAsString());
            }
        }
        return Z3.Answer.decided(status, values);
    }

    private void keep(Key key, Z3.Answer answer) throws IOException {
        JsonObject json = new JsonObject();
        json.addProperty("key", key.sha256);
        json.addProperty("status", answer.status());
        JsonObject values = new JsonObject();
        for (Map.Entry<String, String> value : answer.values().entrySet()) {
            String canonical = key.names.get(value.getKey());
            if (canonical != null) {
                values.addProperty(canonical, value.getValue());
            }
        }
        json.add("values", values);
        Files.createDirectories(dir);
        Path part = Files.createTempFile(dir, key.sha256, ".part");
        try {
            Files.write(part, (json + "\n").getBytes(StandardCharsets.UTF_8));
            Files.move(part, dir.resolve(key.sha256 + ".json"),
                    StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } finally {
            Files.deleteIfExists(part);
        }
    }
}
