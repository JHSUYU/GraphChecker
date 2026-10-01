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
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The libraries' environment boundaries, shipped with the engine in one file
 * ({@value #RESOURCE}) rather than declared per case: a library is the same
 * wherever a system calls it (SYMBOL-SCOPE §4.2).  One row per line; each
 * states {@code schemaVersion} 1 and its {@code kind}, and is keyed by where
 * it was read ({@code library-catalog.jsonl:<line>}), the shape
 * {@code contract.WireDeclarations} reads declaration rows in.  A malformed
 * row, a member its kind does not have and a row stated twice are refused,
 * naming the row, never skipped.
 *
 * <ul>
 *   <li>{@code DOOR} ({@code transport, direction, method, before | after,
 *       faults}): a transport's fault point ({@link DoorWeave}), at the first
 *       call of {@code before} or {@code after} in {@code method}, one
 *       marker per fault kind in order.  Rows of one door method (its
 *       transport, direction, class and name) are that method's signatures
 *       on different library lines (Hadoop IPC's response wait is a
 *       {@code CompletableFuture} on trunk, a monitor on 3.4).</li>
 *   <li>{@code CONFIG_SOURCE} ({@code method, keyArg, defaultArg?}): a
 *       configuration getter, argument {@code keyArg} (a String) its key and
 *       {@code defaultArg} its default.</li>
 * </ul>
 */
public final class LibraryCatalog {
    static final String RESOURCE =
            "/edu/uva/liftlab/graphchecker/library-catalog.jsonl";
    /** The system property naming a system's own DOOR rows (its {@code
     *  experiments/<system>/doors.jsonl}), which override the catalog's. */
    public static final String SYSTEM_DOORS = "causynth.system.doors";
    static final int SCHEMA_VERSION = 1;
    static final String DOOR = "DOOR";
    static final String CONFIG_SOURCE = "CONFIG_SOURCE";

    private static final Map<String, Set<String>> MEMBERS =
            new LinkedHashMap<>();

    static {
        MEMBERS.put(DOOR, names("transport", "direction", "method", "before",
                "after", "faults"));
        MEMBERS.put(CONFIG_SOURCE, names("method", "keyArg", "defaultArg"));
    }

    /** A transport or direction name. */
    private static final Pattern NAME = Pattern.compile("[A-Z][A-Z0-9_]*");
    /** A Soot method signature: its class, name and parameter types. */
    private static final Pattern SIGNATURE = Pattern.compile(
            "<([^:\\s]+): \\S+ ([^(\\s]+)\\(([^)]*)\\)>");
    /** A class name, nested ({@code $}) or not. */
    private static final Pattern CLASS =
            Pattern.compile("[A-Za-z_$][\\w$]*(\\.[A-Za-z_$][\\w$]*)+");

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

        private Door(String transport, String direction, String method,
                     String anchor, boolean after, List<String> faults) {
            this.transport = transport;
            this.direction = direction;
            this.method = method;
            this.anchor = anchor;
            this.after = after;
            this.faults = Collections.unmodifiableList(faults);
        }

        /** {@code FAULT:<TRANSPORT>:<DIRECTION>}, the markers' stem. */
        public String name() {
            return "FAULT:" + transport + ":" + direction;
        }

        /** The outermost class of the door method: the unit a scope
         *  takes, with its nested classes. */
        public String family() {
            String owner = owner(method);
            int nested = owner.indexOf('$');
            return nested < 0 ? owner : owner.substring(0, nested);
        }

        /** The door method this row is one library line's signature of. */
        String doorMethod() {
            Matcher member = SIGNATURE.matcher(method);
            member.matches();
            return name() + " at " + member.group(1) + "#" + member.group(2);
        }
    }

    /**
     * Every DOOR this run weaves, in file order: the engine's catalog, where
     * the system's own doors ({@value #SYSTEM_DOORS}) replace the catalog's
     * rows of their transport and direction.
     */
    public static List<Door> doors() {
        List<Door> known = doors;
        if (known == null) {
            try (InputStream in = LibraryCatalog.class
                    .getResourceAsStream(RESOURCE)) {
                if (in == null) {
                    throw new IllegalStateException(
                            "library catalog missing from the engine: "
                                    + RESOURCE);
                }
                known = doors(rows(new BufferedReader(new InputStreamReader(
                        in, StandardCharsets.UTF_8)), RESOURCE.substring(
                        RESOURCE.lastIndexOf('/') + 1)));
            } catch (IOException unreadable) {
                throw new UncheckedIOException(unreadable);
            }
            String system = System.getProperty(SYSTEM_DOORS, "").trim();
            if (!system.isEmpty()) {
                Path file = Paths.get(system);
                try (BufferedReader reader = Files.newBufferedReader(file,
                        StandardCharsets.UTF_8)) {
                    known = overridden(known, doors(rows(reader,
                            file.getFileName().toString())));
                } catch (IOException unreadable) {
                    throw new UncheckedIOException(unreadable);
                }
            }
            doors = known;
        }
        return known;
    }

    /**
     * The catalog's doors with the system's in place of every catalog row
     * of a transport and direction the system states: a system whose own
     * message or store hook follows the library's call (Solr's
     * {@code SolrZkClient#causynthWrote}, {@code CausynthHttp#response})
     * places the door after that hook, so the fault keeps the pairing the
     * hook files.
     */
    static List<Door> overridden(List<Door> catalog, List<Door> system) {
        Set<String> replaced = new LinkedHashSet<>();
        for (Door door : system) replaced.add(door.name());
        List<Door> doors = new ArrayList<>();
        for (Door door : catalog) {
            if (!replaced.contains(door.name())) doors.add(door);
        }
        doors.addAll(system);
        return Collections.unmodifiableList(doors);
    }

    /** The door transports: a {@code FAULT:<TRANSPORT>:...} marker is a
     *  door's exactly when its transport is one of these. */
    public static Set<String> transports() {
        Set<String> found = new LinkedHashSet<>();
        for (Door door : doors()) found.add(door.transport);
        return found;
    }

    /** A catalog's rows, each keyed by {@code <file>:<line>}. */
    static Map<String, JsonObject> rows(BufferedReader reader, String file)
            throws IOException {
        Map<String, JsonObject> rows = new LinkedHashMap<>();
        String line;
        int number = 0;
        while ((line = reader.readLine()) != null) {
            number++;
            if (line.trim().isEmpty()) continue;
            String at = file + ":" + number;
            JsonElement row;
            try {
                row = JsonParser.parseString(line);
            } catch (RuntimeException malformed) {
                throw refused(at, malformed.getMessage(), malformed);
            }
            if (!row.isJsonObject()) throw refused(at, "not an object", null);
            rows.put(at, row.getAsJsonObject());
        }
        return rows;
    }

    /** The DOOR rows of a catalog's rows, every row checked by its kind. */
    static List<Door> doors(Map<String, JsonObject> rows) {
        List<Door> doors = new ArrayList<>();
        Map<String, String> declaredAt = new LinkedHashMap<>();
        for (Map.Entry<String, JsonObject> entry : rows.entrySet()) {
            try {
                JsonObject row = entry.getValue();
                String identity;
                if (DOOR.equals(kind(row))) {
                    Door door = door(row);
                    doors.add(door);
                    identity = door.name() + " " + door.method;
                } else {
                    identity = CONFIG_SOURCE + " " + configSource(row);
                }
                String first = declaredAt.putIfAbsent(identity,
                        entry.getKey());
                if (first != null) {
                    throw new IllegalArgumentException(identity
                            + " is stated again; first at " + first);
                }
            } catch (RuntimeException malformed) {
                throw refused(entry.getKey(), malformed.getMessage(),
                        malformed);
            }
        }
        return Collections.unmodifiableList(doors);
    }

    private static String kind(JsonObject row) {
        JsonElement version = row.get("schemaVersion");
        if (version == null || !version.isJsonPrimitive()
                || !version.getAsJsonPrimitive().isNumber()
                || !String.valueOf(SCHEMA_VERSION).equals(
                        version.getAsString())) {
            throw new IllegalArgumentException("states schemaVersion "
                    + version + "; this build reads " + SCHEMA_VERSION);
        }
        String kind = text(row, "kind");
        Set<String> members = MEMBERS.get(kind);
        if (members == null) {
            throw new IllegalArgumentException("kind " + kind + " is none of "
                    + MEMBERS.keySet());
        }
        for (String member : row.keySet()) {
            if (!members.contains(member)) {
                throw new IllegalArgumentException(kind + " has no member "
                        + member);
            }
        }
        return kind;
    }

    private static Door door(JsonObject row) {
        String before = optionalText(row, "before");
        String after = optionalText(row, "after");
        if ((before == null) == (after == null)) {
            throw new IllegalArgumentException(
                    "a door states one of before and after");
        }
        JsonElement listed = row.get("faults");
        if (listed == null || !listed.isJsonArray()
                || listed.getAsJsonArray().size() == 0) {
            throw new IllegalArgumentException(
                    "faults lists the kinds a door throws");
        }
        List<String> faults = new ArrayList<>();
        for (JsonElement kind : listed.getAsJsonArray()) {
            faults.add(matching(CLASS, string(kind, "faults"), "faults")
                    .group());
        }
        return new Door(matching(NAME, text(row, "transport"), "transport")
                .group(), matching(NAME, text(row, "direction"), "direction")
                .group(), signature(text(row, "method")).group(),
                signature(after != null ? after : before).group(),
                after != null, faults);
    }

    /** Checks a CONFIG_SOURCE row; its method. */
    private static String configSource(JsonObject row) {
        Matcher method = signature(text(row, "method"));
        List<String> parameters = method.group(3).isEmpty()
                ? Collections.<String>emptyList()
                : Arrays.asList(method.group(3).split(","));
        int key = index(row, "keyArg", parameters.size());
        if (key < 0 || !"java.lang.String".equals(parameters.get(key))) {
            throw new IllegalArgumentException(
                    "keyArg names the String argument that is the key");
        }
        if (index(row, "defaultArg", parameters.size()) == key) {
            throw new IllegalArgumentException(
                    "defaultArg is another argument than the key");
        }
        return method.group();
    }

    /** An argument index below {@code arity}, or -1 when absent. */
    private static int index(JsonObject row, String member, int arity) {
        JsonElement value = row.get(member);
        if (value == null) return -1;
        if (!value.isJsonPrimitive() || !value.getAsJsonPrimitive().isNumber()
                || !value.getAsString().matches("0|[1-9][0-9]*")
                || Integer.parseInt(value.getAsString()) >= arity) {
            throw new IllegalArgumentException(member + " is an argument "
                    + "index below " + arity + "; got " + value);
        }
        return Integer.parseInt(value.getAsString());
    }

    private static Matcher signature(String signature) {
        return matching(SIGNATURE, signature, "method");
    }

    private static Matcher matching(Pattern pattern, String value,
                                    String member) {
        Matcher matcher = pattern.matcher(value);
        if (!matcher.matches()) {
            throw new IllegalArgumentException(member + " is no "
                    + pattern.pattern() + ": " + value);
        }
        return matcher;
    }

    private static String text(JsonObject row, String member) {
        String stated = optionalText(row, member);
        if (stated == null) {
            throw new IllegalArgumentException("states no " + member);
        }
        return stated;
    }

    /** A string member, or null when absent. */
    private static String optionalText(JsonObject row, String member) {
        JsonElement value = row.get(member);
        return value == null ? null : string(value, member);
    }

    private static String string(JsonElement value, String member) {
        if (!value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isString()) {
            throw new IllegalArgumentException(member + " is not a string: "
                    + value);
        }
        return value.getAsString();
    }

    /** The declaring class of a Soot method signature. */
    private static String owner(String signature) {
        return signature.substring(1, signature.indexOf(": "));
    }

    private static Set<String> names(String... names) {
        Set<String> set = new LinkedHashSet<>(Arrays.asList(names));
        set.add("schemaVersion");
        set.add("kind");
        return set;
    }

    private static IllegalArgumentException refused(String at, String why,
                                                    Throwable cause) {
        return new IllegalArgumentException("library catalog at " + at
                + ": " + why, cause);
    }
}
