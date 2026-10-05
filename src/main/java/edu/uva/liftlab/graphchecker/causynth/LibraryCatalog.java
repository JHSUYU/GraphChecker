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
 * it was read ({@code library-catalog.jsonl:<line>}).  A malformed
 * row, a member its kind does not have and a row stated twice are refused,
 * naming the row, never skipped.
 *
 * <ul>
 *   <li>{@code DOOR} ({@code transport, direction, method?, before | after,
 *       faults | result, sites?}): a transport's fault point ({@link
 *       DoorWeave}), at the first call of {@code before} or {@code after} in
 *       {@code method}, one marker per fault kind in order.  Rows of one
 *       door method (its transport, direction, class and name) are that
 *       method's signatures on different library lines (Hadoop IPC's
 *       response wait is a {@code CompletableFuture} on trunk, a monitor on
 *       3.4).  A door with no {@code method} is a library call whose outcome
 *       each caller reads where it makes it (a DataTransfer op's response,
 *       parsed by every side that sent the op): it sits at the first call of
 *       its anchor in every analysed method making one -- or, with {@code
 *       sites} {@value #DEMANDED}, only at the calls the root demand chose
 *       ({@link DemandedDoors}: a local file operation, {@code LOCAL_IO}),
 *       before the call, so a failed operation never happens.  Such a door
 *       states either the kinds it throws or the failing {@code result} the
 *       call returns instead ({@code false}, {@code null}: {@code
 *       File#renameTo}, {@code File#list}).</li>
 *   <li>{@code CONFIG_SOURCE} ({@code method, keyArg, defaultArg?}): a
 *       configuration getter, argument {@code keyArg} (a String) its key and
 *       {@code defaultArg} its default ({@link ConfigRoots}).</li>
 *   <li>{@code CONFIG_FIELD_OWNER} ({@code class}): a class whose every
 *       field is configuration, each its own key: a configuration object
 *       built from a file no getter of the catalog reads (Solr's {@code
 *       NodeConfig}, {@code CloudConfig}).</li>
 * </ul>
 */
public final class LibraryCatalog {
    static final String RESOURCE =
            "/edu/uva/liftlab/graphchecker/library-catalog.jsonl";
    /** The system property naming a system's own HOOK rows (its {@code
     *  experiments/<system>/doors.jsonl}), which place catalog doors after
     *  the system's own message or store hook. */
    public static final String SYSTEM_DOORS = "causynth.system.doors";
    static final int SCHEMA_VERSION = 1;
    static final String DOOR = "DOOR";
    static final String CONFIG_SOURCE = "CONFIG_SOURCE";
    static final String CONFIG_FIELD_OWNER = "CONFIG_FIELD_OWNER";
    /** A system's own row: where its hook sits relative to a catalog door. */
    static final String HOOK = "HOOK";
    /** A door's {@code sites}: only the calls the root demand chose. */
    static final String DEMANDED = "DEMANDED";

    private static final Map<String, Set<String>> MEMBERS =
            new LinkedHashMap<>();

    static {
        MEMBERS.put(DOOR, names("transport", "direction", "method", "before",
                "after", "faults", "result", "sites"));
        MEMBERS.put(CONFIG_SOURCE, names("method", "keyArg", "defaultArg"));
        MEMBERS.put(CONFIG_FIELD_OWNER, names("class"));
        MEMBERS.put(HOOK, names("transport", "direction", "door", "method",
                "after"));
    }

    /** A transport or direction name. */
    private static final Pattern NAME = Pattern.compile("[A-Z][A-Z0-9_]*");
    /** A Soot method signature: its class, name and parameter types. */
    private static final Pattern SIGNATURE = Pattern.compile(
            "<([^:\\s]+): \\S+ ([^(\\s]+)\\(([^)]*)\\)>");
    /** A class name, nested ({@code $}) or not. */
    private static final Pattern CLASS =
            Pattern.compile("[A-Za-z_$][\\w$]*(\\.[A-Za-z_$][\\w$]*)+");

    /** The engine's catalog, read once. */
    private static volatile Contents shipped;
    /** Its doors, each placed after its system's hook. */
    private static volatile List<Door> doors;

    private LibraryCatalog() {
    }

    /** One catalog's rows, by kind, in file order. */
    static final class Contents {
        final List<Door> doors;
        final List<ConfigSource> configSources;
        final Set<String> configFieldOwners;

        private Contents(List<Door> doors, List<ConfigSource> configSources,
                         Set<String> configFieldOwners) {
            this.doors = Collections.unmodifiableList(doors);
            this.configSources = Collections.unmodifiableList(configSources);
            this.configFieldOwners =
                    Collections.unmodifiableSet(configFieldOwners);
        }
    }

    /** One configuration getter of a library. */
    public static final class ConfigSource {
        /** Its Soot signature. */
        public final String method;
        /** The argument that is the key, a String. */
        public final int keyArg;
        /** The argument that is the default, or -1. */
        public final int defaultArg;

        private ConfigSource(String method, int keyArg, int defaultArg) {
            this.method = method;
            this.keyArg = keyArg;
            this.defaultArg = defaultArg;
        }
    }

    /** What a demanded door's call returns instead of failing by a
     *  throw: nothing (it throws its kinds), {@code false} or {@code null}. */
    public enum Result { NONE, FALSE, NULL }

    /** One fault point of a library transport. */
    public static final class Door {
        public final String transport;
        public final String direction;
        /** The Soot signature of the method the door is woven into; null
         *  for a door at every call of its anchor ({@link #atCalls}). */
        public final String method;
        /** The call the door sits at, and on which side of it. */
        public final String anchor;
        public final boolean after;
        /** The kinds thrown, in order; none for a failing result. */
        public final List<String> faults;
        /** Woven only at the calls the root demand chose ({@value
         *  #DEMANDED}). */
        public final boolean demanded;
        /** The failing result, or {@link Result#NONE}. */
        public final Result result;

        private Door(String transport, String direction, String method,
                     String anchor, boolean after, List<String> faults,
                     boolean demanded, Result result) {
            this.transport = transport;
            this.direction = direction;
            this.method = method;
            this.anchor = anchor;
            this.after = after;
            this.faults = Collections.unmodifiableList(faults);
            this.demanded = demanded;
            this.result = result;
        }

        /** {@code FAULT:<TRANSPORT>:<DIRECTION>}, the markers' stem. */
        public String name() {
            return "FAULT:" + transport + ":" + direction;
        }

        /** Whether the door sits at every analysed call of its anchor
         *  rather than in one door method. */
        public boolean atCalls() {
            return method == null;
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

        /** Where the door sits: its method, every call of its anchor, or
         *  the demanded ones. */
        String place() {
            return demanded ? "the demanded calls of " + anchor
                    : atCalls() ? "every call of " + anchor : method;
        }
    }

    /**
     * Every DOOR this run weaves, in file order: the engine's catalog, each
     * placed after its system's own hook where the system states one
     * ({@value #SYSTEM_DOORS}, {@link #placed}).
     */
    public static List<Door> doors() {
        List<Door> known = doors;
        if (known == null) {
            known = shipped().doors;
            String system = System.getProperty(SYSTEM_DOORS, "").trim();
            if (!system.isEmpty()) {
                Path file = Paths.get(system);
                try (BufferedReader reader = Files.newBufferedReader(file,
                        StandardCharsets.UTF_8)) {
                    known = placed(known, hooks(rows(reader,
                            file.getFileName().toString())));
                } catch (IOException unreadable) {
                    throw new UncheckedIOException(unreadable);
                }
            }
            doors = known;
        }
        return known;
    }

    /** The configuration getters of the libraries, in file order. */
    public static List<ConfigSource> configSources() {
        return shipped().configSources;
    }

    /** The classes whose every field is configuration. */
    public static Set<String> configFieldOwners() {
        return shipped().configFieldOwners;
    }

    /** The engine's catalog ({@value #RESOURCE}), read once. */
    private static Contents shipped() {
        Contents known = shipped;
        if (known != null) return known;
        try (InputStream in = LibraryCatalog.class
                .getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException(
                        "library catalog missing from the engine: "
                                + RESOURCE);
            }
            known = read(rows(new BufferedReader(new InputStreamReader(
                    in, StandardCharsets.UTF_8)), RESOURCE.substring(
                    RESOURCE.lastIndexOf('/') + 1)));
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        shipped = known;
        return known;
    }

    /**
     * One system's HOOK row: the catalog door ({@code transport},
     * {@code direction}, {@code door}, its method) is woven in {@code method}
     * after the first call of {@code after}, the system's own message or
     * store hook, instead of at its library anchor.  It states where the
     * hook sits, nothing else: the door's kinds are the catalog's, and a
     * door no hook names keeps its anchor.
     */
    static final class Hook {
        final String transport;
        final String direction;
        final String door;
        final String method;
        final String after;

        private Hook(String transport, String direction, String door,
                     String method, String after) {
            this.transport = transport;
            this.direction = direction;
            this.door = door;
            this.method = method;
            this.after = after;
        }

        boolean places(Door catalog) {
            return catalog.transport.equals(transport)
                    && catalog.direction.equals(direction)
                    && door.equals(catalog.method);
        }
    }

    /**
     * The catalog's doors, each a system hook names placed after that hook,
     * so the fault keeps the pairing the hook files (Solr's ZooKeeper writes
     * after {@code SolrZkClient#causynthWrote}).  A hook naming no catalog
     * door is refused by name.
     */
    static List<Door> placed(List<Door> catalog, List<Hook> hooks) {
        List<Door> doors = new ArrayList<>();
        Set<Hook> used = new LinkedHashSet<>();
        for (Door door : catalog) {
            Door placed = door;
            for (Hook hook : hooks) {
                if (!hook.places(door)) continue;
                placed = new Door(door.transport, door.direction,
                        hook.method, hook.after, true, door.faults,
                        door.demanded, door.result);
                used.add(hook);
            }
            doors.add(placed);
        }
        for (Hook hook : hooks) {
            if (!used.contains(hook)) {
                throw new IllegalArgumentException("HOOK " + hook.transport
                        + ":" + hook.direction + " names no catalog door "
                        + hook.door);
            }
        }
        return Collections.unmodifiableList(doors);
    }

    /** A system's HOOK rows; any other kind there is refused. */
    static List<Hook> hooks(Map<String, JsonObject> rows) {
        List<Hook> hooks = new ArrayList<>();
        for (Map.Entry<String, JsonObject> entry : rows.entrySet()) {
            try {
                JsonObject row = entry.getValue();
                if (!HOOK.equals(kind(row))) {
                    throw new IllegalArgumentException("a system states "
                            + "where its hooks are (HOOK), never a door");
                }
                hooks.add(new Hook(matching(NAME, text(row, "transport"),
                        "transport").group(), matching(NAME, text(row,
                        "direction"), "direction").group(),
                        signature(text(row, "door")).group(),
                        signature(text(row, "method")).group(),
                        signature(text(row, "after")).group()));
            } catch (RuntimeException malformed) {
                throw refused(entry.getKey(), malformed.getMessage(),
                        malformed);
            }
        }
        return hooks;
    }

    /** Whether a marker name is a demanded door's ({@code
     *  FAULT:<TRANSPORT>:..} of a transport whose doors are demanded). */
    public static boolean demandedMarker(String name) {
        return doorMarker(name, true);
    }

    /** Whether a marker name is a message door's ({@code
     *  FAULT:<TRANSPORT>:..} of a transport whose doors are not demanded):
     *  its fault ends an exchange, a local file operation's ends none. */
    public static boolean exchangeMarker(String name) {
        return doorMarker(name, false);
    }

    /** Whether a marker name is a door's of a transport whose doors are
     *  {@code demanded}, or are not. */
    private static boolean doorMarker(String name, boolean demanded) {
        String[] parts = name == null ? new String[0] : name.split(":", -1);
        if (parts.length < 2 || !"FAULT".equals(parts[0])) return false;
        for (Door door : doors()) {
            if (door.demanded == demanded
                    && door.transport.equals(parts[1])) {
                return true;
            }
        }
        return false;
    }

    /** The demanded door at calls of {@code callee}, or null. */
    public static Door demandedDoor(String callee) {
        for (Door door : doors()) {
            if (door.demanded && door.anchor.equals(callee)) return door;
        }
        return null;
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

    /** A catalog's rows by kind, every row checked by its kind. */
    static Contents read(Map<String, JsonObject> rows) {
        List<Door> doors = new ArrayList<>();
        List<ConfigSource> configSources = new ArrayList<>();
        Set<String> owners = new LinkedHashSet<>();
        Map<String, String> declaredAt = new LinkedHashMap<>();
        for (Map.Entry<String, JsonObject> entry : rows.entrySet()) {
            try {
                JsonObject row = entry.getValue();
                String identity;
                String kind = kind(row);
                if (HOOK.equals(kind)) {
                    throw new IllegalArgumentException("a HOOK is a "
                            + "system's row, not the catalog's");
                }
                if (DOOR.equals(kind)) {
                    Door door = door(row);
                    doors.add(door);
                    identity = door.name() + " " + door.place();
                } else if (CONFIG_SOURCE.equals(kind)) {
                    ConfigSource source = configSource(row);
                    configSources.add(source);
                    identity = CONFIG_SOURCE + " " + source.method;
                } else {
                    String owner = matching(CLASS, text(row, "class"),
                            "class").group();
                    owners.add(owner);
                    identity = CONFIG_FIELD_OWNER + " " + owner;
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
        return new Contents(doors, configSources, owners);
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
        String method = optionalText(row, "method");
        String sites = optionalText(row, "sites");
        boolean demanded = sites != null;
        if (demanded && (!DEMANDED.equals(sites) || method != null
                || before == null)) {
            throw new IllegalArgumentException("sites " + DEMANDED
                    + " is a door at calls with no method, before its call:"
                    + " a failed operation never happens");
        }
        JsonElement listed = row.get("faults");
        Result result = result(row.get("result"), row.has("result"));
        if (result != Result.NONE && (!demanded || listed != null)) {
            throw new IllegalArgumentException("a failing result belongs "
                    + "to a demanded door that throws no faults");
        }
        List<String> faults = new ArrayList<>();
        if (result == Result.NONE) {
            if (listed == null || !listed.isJsonArray()
                    || listed.getAsJsonArray().size() == 0) {
                throw new IllegalArgumentException(
                        "faults lists the kinds a door throws");
            }
            for (JsonElement kind : listed.getAsJsonArray()) {
                faults.add(matching(CLASS, string(kind, "faults"), "faults")
                        .group());
            }
        }
        return new Door(matching(NAME, text(row, "transport"), "transport")
                .group(), matching(NAME, text(row, "direction"), "direction")
                .group(), method == null ? null : signature(method).group(),
                signature(after != null ? after : before).group(),
                after != null, faults, demanded, result);
    }

    /** A door's {@code result}: {@code false} or {@code null} when stated. */
    private static Result result(JsonElement value, boolean stated) {
        if (!stated) return Result.NONE;
        if (value.isJsonNull()) return Result.NULL;
        if (value.isJsonPrimitive() && value.getAsJsonPrimitive().isBoolean()
                && !value.getAsBoolean()) {
            return Result.FALSE;
        }
        throw new IllegalArgumentException("result is false or null: "
                + value);
    }

    /** One CONFIG_SOURCE row, checked. */
    private static ConfigSource configSource(JsonObject row) {
        Matcher method = signature(text(row, "method"));
        List<String> parameters = method.group(3).isEmpty()
                ? Collections.<String>emptyList()
                : Arrays.asList(method.group(3).split(","));
        int key = index(row, "keyArg", parameters.size());
        if (key < 0 || !"java.lang.String".equals(parameters.get(key))) {
            throw new IllegalArgumentException(
                    "keyArg names the String argument that is the key");
        }
        int fallback = index(row, "defaultArg", parameters.size());
        if (fallback == key) {
            throw new IllegalArgumentException(
                    "defaultArg is another argument than the key");
        }
        return new ConfigSource(method.group(), key, fallback);
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
