package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.Z3;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.Supplier;

/**
 * THE SOLVER KEY: z3's answers by query text, one iteration's
 * ({@code <iteration>/solved/<sha256>.json}).  A flip's ask is the text its
 * solver sends (body, check-sat, get-value: {@link Z3#modelQuery}), and what
 * z3 decides of it -- unsat, or sat and a model's values of the symbols the
 * text names -- is a fact of that text alone, whatever obligation, world,
 * task, focus or plan generation built it: the first decided answer is kept
 * under the text's sha256, and every later ask of the same text, by any
 * solver of the iteration on any host, the hard lane's too, is answered with
 * it and runs no z3 (SOLR-18413 b05: 312 of 519 solver-decided asks were
 * texts asked before).  What a question settles and what its replay is
 * given stay its own ({@code ObligationFactory#question}, the replay key):
 * the answer is mapped for each ask as z3's own would be, so a kept answer
 * writes the files a z3 run deciding the same writes.
 *
 * <p>A kept model is ONE model of the text, as a z3 run gives one: each run
 * races two engines and answers with the one that decided first ({@link
 * Z3}), so which model a run gives was never fixed by the text.  Only a
 * decided answer is kept: a timeout, a memout, unknown, an error or engines
 * that disagree say nothing of the text, and the next ask runs z3 again at
 * its own budget and room.  A kept answer carries no core: every ask it
 * answers asks none.</p>
 *
 * <p>An entry is written whole or not at all (a file of its own, moved into
 * place), and two asks deciding one text at once each write a decided answer
 * of it; a reader on another host that does not see an entry yet asks z3,
 * as before the store.</p>
 */
final class Solved {
    /** Its directory, in the iteration. */
    static final String DIR = "solved";
    /** Keeps nothing: an ask whose record names no store. */
    static final Solved NONE = new Solved(null);

    private final Path dir;

    private Solved(Path dir) {
        this.dir = dir;
    }

    /** One iteration's store. */
    static Solved in(Path iteration) {
        return new Solved(iteration.resolve(DIR));
    }

    /** A store by its directory, as a hard-lane record names it; null:
     *  {@link #NONE}. */
    static Solved at(Path dir) {
        return dir == null ? NONE : new Solved(dir);
    }

    /** Its directory, or null for {@link #NONE}. */
    Path dir() {
        return dir;
    }

    /**
     * z3's answer to the text of this sha256: the one kept, else what
     * {@code z3} answers, kept once decided.
     */
    Z3.Answer answer(String querySha256, Supplier<Z3.Answer> z3)
            throws IOException {
        Z3.Answer kept = kept(querySha256);
        if (kept != null) {
            System.err.println("causynth: query " + querySha256
                    + " answered " + kept.status() + " as kept in " + dir
                    + ": no z3 run");
            return kept;
        }
        Z3.Answer answer = z3.get();
        if (dir != null && answer.decided()) keep(querySha256, answer);
        return answer;
    }

    /** The answer kept for this text, or null. */
    private Z3.Answer kept(String querySha256) throws IOException {
        if (dir == null) return null;
        JsonObject json;
        try {
            json = ExploreCodec.readObject(dir.resolve(querySha256 + ".json"));
        } catch (NoSuchFileException none) {
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
