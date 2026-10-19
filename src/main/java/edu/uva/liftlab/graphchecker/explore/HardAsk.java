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

final class HardAsk {
    static final String FILE = "obligation_ask.json";

    final String obligationId;
    final String gapSession;
    final String question;
    final String unsatDetail;
    final List<GapRow> gaps;
    final List<String> modelSymbols;
    final String querySha256;
    final Solved.Key solvedKey;
    final Path solved;

    HardAsk(String obligationId, String gapSession, String question,
            String unsatDetail, List<GapRow> gaps, List<String> modelSymbols,
            String querySha256, Solved.Key solvedKey, Path solved) {
        this.obligationId = obligationId;
        this.gapSession = gapSession;
        this.question = question;
        this.unsatDetail = unsatDetail;
        this.gaps = Collections.unmodifiableList(new ArrayList<GapRow>(gaps));
        this.modelSymbols = Collections.unmodifiableList(
                new ArrayList<String>(modelSymbols));
        this.querySha256 = querySha256;
        this.solvedKey = solvedKey;
        this.solved = solved;
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
        json.addProperty("querySha256", querySha256);
        json.addProperty("solvedKey", solvedKey.sha256);
        JsonObject names = new JsonObject();
        for (java.util.Map.Entry<String, String> name
                : solvedKey.names.entrySet()) {
            names.addProperty(name.getKey(), name.getValue());
        }
        json.add("solvedNames", names);
        json.addProperty("solved", solved == null ? "" : solved.toString());
        Path part = file.resolveSibling(file.getFileName() + ".part");
        Files.write(part, (json + "\n").getBytes(StandardCharsets.UTF_8));
        Files.move(part, file, java.nio.file.StandardCopyOption.ATOMIC_MOVE,
                java.nio.file.StandardCopyOption.REPLACE_EXISTING);
    }

    static final class Model {
        static final String FILE = "obligation_model.json";

        final String querySha256;
        final java.util.Map<String, String> values;
        final long budgetMillis;
        final int roomMb;

        Model(String querySha256, java.util.Map<String, String> values,
              long budgetMillis, int roomMb) {
            this.querySha256 = querySha256;
            this.values = Collections.unmodifiableMap(
                    new java.util.LinkedHashMap<String, String>(values));
            this.budgetMillis = budgetMillis;
            this.roomMb = roomMb;
        }

        void write(Path file) throws IOException {
            JsonObject json = new JsonObject();
            json.addProperty("querySha256", querySha256);
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
            return new Model(JsonFields.primitiveString(json, "querySha256"),
                    values, json.get("budgetMillis").getAsLong(),
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
        java.util.Map<String, String> names =
                new java.util.LinkedHashMap<String, String>();
        for (java.util.Map.Entry<String, JsonElement> name
                : JsonFields.object(json, "solvedNames").entrySet()) {
            names.put(name.getKey(), name.getValue().getAsString());
        }
        String solved = JsonFields.primitiveString(json, "solved");
        return new HardAsk(JsonFields.primitiveString(json, "obligationId"),
                JsonFields.primitiveString(json, "gapSession"),
                JsonFields.primitiveString(json, "question"),
                JsonFields.primitiveString(json, "unsatDetail"), gaps,
                symbols, JsonFields.primitiveString(json, "querySha256"),
                new Solved.Key(JsonFields.primitiveString(json, "solvedKey"),
                        names),
                solved.isEmpty() ? null : java.nio.file.Paths.get(solved));
    }
}
