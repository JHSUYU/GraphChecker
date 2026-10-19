package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.Z3;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.FileSystemException;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
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

    Z3.Answer answer(String querySha256, Collection<String> modelSymbols,
                     Supplier<Z3.Answer> z3) throws IOException {
        Z3.Answer kept = kept(querySha256);
        if (kept != null && whole(kept, modelSymbols)) {
            System.err.println("causynth: query " + querySha256
                    + " answered " + kept.status() + " as kept in " + dir
                    + ": no z3 run");
            return kept;
        }
        Z3.Answer answer = z3.get();
        if (dir != null && whole(answer, modelSymbols)) {
            try {
                keep(querySha256, answer);
            } catch (IOException unwritten) {
                System.err.println("causynth: query " + querySha256
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

    private Z3.Answer kept(String querySha256) throws IOException {
        if (dir == null) return null;
        JsonObject json;
        try {
            json = ExploreCodec.readObject(dir.resolve(querySha256 + ".json"));
        } catch (FileSystemException unread) {
            return null;
        }
        if (!querySha256.equals(JsonFields.primitiveString(json,
                "querySha256"))) {
            throw new IOException("the answer kept as " + querySha256
                    + " in " + dir + " is of query "
                    + JsonFields.primitiveString(json, "querySha256"));
        }
        String status = JsonFields.primitiveString(json, "status");
        Map<String, String> values = new LinkedHashMap<String, String>();
        for (Map.Entry<String, JsonElement> value
                : JsonFields.object(json, "values").entrySet()) {
            values.put(value.getKey(), value.getValue().getAsString());
        }
        return Z3.Answer.decided(status, values);
    }

    private void keep(String querySha256, Z3.Answer answer)
            throws IOException {
        JsonObject json = new JsonObject();
        json.addProperty("querySha256", querySha256);
        json.addProperty("status", answer.status());
        JsonObject values = new JsonObject();
        for (Map.Entry<String, String> value : answer.values().entrySet()) {
            values.addProperty(value.getKey(), value.getValue());
        }
        json.add("values", values);
        Files.createDirectories(dir);
        Path part = Files.createTempFile(dir, querySha256, ".part");
        try {
            Files.write(part, (json + "\n").getBytes(StandardCharsets.UTF_8));
            Files.move(part, dir.resolve(querySha256 + ".json"),
                    StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } finally {
            Files.deleteIfExists(part);
        }
    }
}
