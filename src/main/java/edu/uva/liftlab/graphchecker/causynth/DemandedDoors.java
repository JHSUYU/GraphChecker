package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

final class DemandedDoors {
    static final String FILE = "io_doors.jsonl";
    static final String PROPERTY = "causynth.io.doors";
    static final String KIND = "DEMANDED_DOOR";

    static final class Site {
        final String caller;
        final String callee;
        final int ordinal;
        final int distance;
        final String reach;
        final List<String> via;

        Site(String caller, String callee, int ordinal, int distance,
             String reach, List<String> via) {
            this.caller = caller;
            this.callee = callee;
            this.ordinal = ordinal;
            this.distance = distance;
            this.reach = reach;
            this.via = Collections.unmodifiableList(new ArrayList<>(via));
        }

        String key() {
            return caller + "|" + callee + "|" + ordinal;
        }

        JsonObject row() {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", KIND);
            row.addProperty("caller", caller);
            row.addProperty("callee", callee);
            row.addProperty("ordinal", ordinal);
            row.addProperty("distance", distance);
            row.addProperty("reach", reach);
            com.google.gson.JsonArray chain = new com.google.gson.JsonArray();
            for (String method : via) chain.add(method);
            row.add("via", chain);
            return row;
        }
    }

    private DemandedDoors() {
    }

    static List<Site> woven() {
        String file = System.getProperty(PROPERTY, "").trim();
        return file.isEmpty() ? Collections.<Site>emptyList()
                : read(Paths.get(file));
    }

    static List<Site> read(Path file) {
        List<Site> sites = new ArrayList<>();
        if (!Files.isRegularFile(file)) return sites;
        try {
            for (JsonObject row : ArtifactIO.readJsonl(file)) {
                if (!KIND.equals(text(row, "kind"))) {
                    throw new IllegalStateException("DEMANDED_DOOR_ROW: "
                            + file + ": " + row);
                }
                List<String> via = new ArrayList<>();
                for (com.google.gson.JsonElement method
                        : row.getAsJsonArray("via")) {
                    via.add(method.getAsString());
                }
                if (via.isEmpty()) throw new IllegalStateException("no via");
                sites.add(new Site(text(row, "caller"), text(row, "callee"),
                        row.get("ordinal").getAsInt(),
                        row.get("distance").getAsInt(), text(row, "reach"),
                        via));
            }
        } catch (IOException | RuntimeException unreadable) {
            throw new IllegalStateException("DEMANDED_DOOR_ROW: " + file
                    + " is unreadable: " + unreadable.getMessage(),
                    unreadable);
        }
        return sites;
    }

    static void write(Path file, List<Site> sites) {
        List<JsonObject> rows = new ArrayList<>();
        for (Site site : sites) rows.add(site.row());
        try {
            ArtifactIO.replaceJsonl(file, rows);
        } catch (IOException unwritable) {
            throw new UncheckedIOException(unwritable);
        }
    }

    private static String text(JsonObject row, String member) {
        if (!row.has(member) || !row.get(member).isJsonPrimitive()) {
            throw new IllegalStateException("states no " + member);
        }
        return row.get(member).getAsString();
    }
}
