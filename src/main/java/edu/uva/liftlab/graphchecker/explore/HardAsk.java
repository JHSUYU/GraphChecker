package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * THE HARD LANE'S INPUT: what a flip's first ask, undecided at its budget by
 * time or by z3's memory cap, leaves beside its query ({@code
 * obligation_query.smt2}), so that its ask at the full budget runs z3 alone,
 * in a JVM that reads no corpus ({@code ObligationSolverMain --decide}), and
 * answers as the corpus would: the question an answer settles, the gaps the
 * query's build stated, what an UNSAT says, and the constants a model
 * names.  A corpus-sized JVM per hard ask held one host each
 * for a 15-20 min corpus read before its z3 started (SGF7-adhoc-39: 21 GB of
 * sessions, 18-21 GB charged per ask, one per host).
 */
final class HardAsk {
    /** Its file, beside the query in the obligation's worker. */
    static final String FILE = "obligation_ask.json";

    final String obligationId;
    /** The session a SOLVER_TIMEOUT or SOLVER_MEMOUT gap is filed under: the
     *  path's. */
    final String gapSession;
    /** The question an UNSAT settles ({@code ObligationFactory#question}). */
    final String question;
    /** What an UNSAT answer says. */
    final String unsatDetail;
    /** The gaps the query's build stated, before any answer's. */
    final List<GapRow> gaps;
    /** The constants a sat answer's model names, in the query's order. */
    final List<String> modelSymbols;

    HardAsk(String obligationId, String gapSession, String question,
            String unsatDetail, List<GapRow> gaps, List<String> modelSymbols) {
        this.obligationId = obligationId;
        this.gapSession = gapSession;
        this.question = question;
        this.unsatDetail = unsatDetail;
        this.gaps = Collections.unmodifiableList(new ArrayList<GapRow>(gaps));
        this.modelSymbols = Collections.unmodifiableList(
                new ArrayList<String>(modelSymbols));
    }

    void write(Path file) throws IOException {
        JsonObject json = new JsonObject();
        json.addProperty("obligationId", obligationId);
        json.addProperty("gapSession", gapSession);
        json.addProperty("question", question);
        json.addProperty("unsatDetail", unsatDetail);
        JsonArray rows = new JsonArray();
        for (GapRow gap : gaps) rows.add(RowCodec.writeGap(gap));
        json.add("gaps", rows);
        JsonArray symbols = new JsonArray();
        for (String symbol : modelSymbols) symbols.add(symbol);
        json.add("modelSymbols", symbols);
        Path part = file.resolveSibling(file.getFileName() + ".part");
        Files.write(part, (json + "\n").getBytes(StandardCharsets.UTF_8));
        Files.move(part, file, java.nio.file.StandardCopyOption.ATOMIC_MOVE,
                java.nio.file.StandardCopyOption.REPLACE_EXISTING);
    }

    /**
     * A sat answer of the hard lane: the model's values, and the budget and
     * z3 room it was asked at.  The flip is finished by its host's solver
     * ({@code ObligationFactory#solve} given it), which plants the model as
     * it is over the query its corpus builds -- the replay decides -- and
     * asks whatever more it asks (the held re-ask) at this budget and room.
     */
    static final class Model {
        static final String FILE = "obligation_model.json";

        final java.util.Map<String, String> values;
        final long budgetMillis;
        final int roomMb;

        Model(java.util.Map<String, String> values, long budgetMillis,
              int roomMb) {
            this.values = Collections.unmodifiableMap(
                    new java.util.LinkedHashMap<String, String>(values));
            this.budgetMillis = budgetMillis;
            this.roomMb = roomMb;
        }

        void write(Path file) throws IOException {
            JsonObject json = new JsonObject();
            json.addProperty("budgetMillis", budgetMillis);
            json.addProperty("roomMb", roomMb);
            JsonObject values = new JsonObject();
            for (java.util.Map.Entry<String, String> value
                    : this.values.entrySet()) {
                values.addProperty(value.getKey(), value.getValue());
            }
            json.add("values", values);
            Path part = file.resolveSibling(file.getFileName() + ".part");
            Files.write(part, (json + "\n").getBytes(StandardCharsets.UTF_8));
            Files.move(part, file,
                    java.nio.file.StandardCopyOption.ATOMIC_MOVE,
                    java.nio.file.StandardCopyOption.REPLACE_EXISTING);
        }

        static Model read(Path file) throws IOException {
            JsonObject json = ExploreCodec.readObject(file);
            java.util.Map<String, String> values =
                    new java.util.LinkedHashMap<String, String>();
            for (java.util.Map.Entry<String, JsonElement> value
                    : JsonFields.object(json, "values").entrySet()) {
                values.put(value.getKey(), value.getValue().getAsString());
            }
            return new Model(values, json.get("budgetMillis").getAsLong(),
                    json.get("roomMb").getAsInt());
        }
    }

    static HardAsk read(Path file) throws IOException {
        JsonObject json = ExploreCodec.readObject(file);
        List<GapRow> gaps = new ArrayList<GapRow>();
        for (JsonElement row : JsonFields.array(json, "gaps")) {
            gaps.add(RowCodec.readGap(row.getAsJsonObject()));
        }
        List<String> symbols = new ArrayList<String>();
        for (JsonElement symbol : JsonFields.array(json, "modelSymbols")) {
            symbols.add(symbol.getAsString());
        }
        return new HardAsk(JsonFields.primitiveString(json, "obligationId"),
                JsonFields.primitiveString(json, "gapSession"),
                JsonFields.primitiveString(json, "question"),
                JsonFields.primitiveString(json, "unsatDetail"), gaps,
                symbols);
    }
}
