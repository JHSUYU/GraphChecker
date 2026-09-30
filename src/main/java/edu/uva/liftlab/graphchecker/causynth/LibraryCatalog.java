package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The libraries' environment boundaries, shipped with the engine (one file,
 * {@value #RESOURCE}) rather than declared per case: a library is the same
 * wherever a system calls it.
 *
 * <ul>
 *   <li>{@code DOOR}: a transport's fault point ({@link DoorWeave}): the
 *       method, the call it sits {@code before} or {@code after} (the first
 *       call of it in the body), and the fault kinds in order.  Several rows
 *       may name one transport and direction: one per door method, or one
 *       per library line whose method differs (Hadoop IPC's response wait is
 *       a {@code CompletableFuture} on trunk, a monitor on 3.4).</li>
 *   <li>{@code CONFIG_SOURCE}: a configuration getter whose argument
 *       {@code keyArg} is the key and {@code defaultArg} (optional) the
 *       default; read by {@code tools/analysis/rootcov.py}.</li>
 * </ul>
 *
 * A door applies where its method's class family is analysed; which library
 * a system calls decides which families its scope takes
 * ({@code plan.ScopeGrowth --doors}).
 */
public final class LibraryCatalog {
    static final String RESOURCE =
            "/edu/uva/liftlab/graphchecker/library-catalog.jsonl";
    static final String DOOR = "DOOR";
    static final String CONFIG_SOURCE = "CONFIG_SOURCE";

    private static volatile List<Door> doors;

    private LibraryCatalog() {
    }

    /** One fault point of a library transport. */
    public static final class Door {
        public final String transport;
        public final String direction;
        /** The Soot signature of the method the door is woven into. */
        public final String method;
        /** The call the door sits at, and on which side of it. */
        public final String anchor;
        public final boolean after;
        public final List<String> faults;

        Door(JsonObject row) {
            transport = text(row, "transport");
            direction = text(row, "direction").toUpperCase();
            method = text(row, "method");
            after = !text(row, "after").isEmpty();
            anchor = after ? text(row, "after") : text(row, "before");
            List<String> kinds = new ArrayList<String>();
            JsonElement listed = row.get("faults");
            if (listed != null && listed.isJsonArray()) {
                for (JsonElement kind : listed.getAsJsonArray()) {
                    kinds.add(kind.getAsString());
                }
            }
            faults = Collections.unmodifiableList(kinds);
            if (transport.isEmpty() || direction.isEmpty()
                    || className(method).isEmpty() || anchor.isEmpty()
                    || (after && !text(row, "before").isEmpty())
                    || faults.isEmpty()) {
                throw new IllegalStateException("library catalog: a DOOR "
                        + "names transport, direction, method, one of "
                        + "before/after and its faults: " + row);
            }
        }

        /** {@code FAULT:<TRANSPORT>:<DIRECTION>}, the markers' stem. */
        public String name() {
            return "FAULT:" + transport + ":" + direction;
        }

        /** The outermost class of the door method: the unit a scope
         *  takes, with its nested classes. */
        public String family() {
            String owner = className(method);
            int nested = owner.indexOf('$');
            return nested < 0 ? owner : owner.substring(0, nested);
        }
    }

    /** Every DOOR row, in file order. */
    public static List<Door> doors() {
        List<Door> known = doors;
        if (known == null) {
            List<Door> read = new ArrayList<Door>();
            for (JsonObject row : rows()) {
                if (DOOR.equals(text(row, "kind"))) read.add(new Door(row));
            }
            doors = known = Collections.unmodifiableList(read);
        }
        return known;
    }

    /** The door transports: a {@code FAULT:<TRANSPORT>:...} marker is a
     *  door's exactly when its transport is one of these. */
    public static Set<String> transports() {
        Set<String> found = new LinkedHashSet<String>();
        for (Door door : doors()) found.add(door.transport);
        return found;
    }

    private static List<JsonObject> rows() {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        try (InputStream in = LibraryCatalog.class
                .getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException(
                        "library catalog missing from the engine: " + RESOURCE);
            }
            BufferedReader reader = new BufferedReader(
                    new InputStreamReader(in, StandardCharsets.UTF_8));
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonObject row = JsonParser.parseString(line)
                        .getAsJsonObject();
                String kind = text(row, "kind");
                if (!DOOR.equals(kind) && !CONFIG_SOURCE.equals(kind)) {
                    throw new IllegalStateException(
                            "library catalog: unknown row kind " + kind);
                }
                rows.add(row);
            }
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        return rows;
    }

    /** The declaring class of a Soot method signature, or "". */
    static String className(String signature) {
        int colon = signature.indexOf(": ");
        return signature.startsWith("<") && colon > 1
                ? signature.substring(1, colon) : "";
    }

    private static String text(JsonObject row, String field) {
        JsonElement value = row.get(field);
        return value == null || value.isJsonNull() ? ""
                : value.getAsString().trim();
    }
}
