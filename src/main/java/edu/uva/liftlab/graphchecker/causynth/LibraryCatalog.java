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

public final class LibraryCatalog {
    static final String RESOURCE =
            "/edu/uva/liftlab/graphchecker/library-catalog.jsonl";
    public static final String SYSTEM_DOORS = "causynth.system.doors";
    static final int SCHEMA_VERSION = 1;
    static final String DOOR = "DOOR";
    static final String CONFIG_SOURCE = "CONFIG_SOURCE";
    static final String CONFIG_FIELD_OWNER = "CONFIG_FIELD_OWNER";
    static final String CODEC = "CODEC";
    static final String MESSAGE = "MESSAGE";
    static final String HOOK = "HOOK";
    static final String PUBLISHED_VIEW = "PUBLISHED_VIEW";
    static final String DEMANDED = "DEMANDED";
    static final String TIMED_WAIT = "TIMED_WAIT";
    static final String SESSION_EXPIRED =
            "org.apache.zookeeper.KeeperException$SessionExpiredException";
    static final String DATA_FLOW = "DATA_FLOW";

    private static final Map<String, Set<String>> MEMBERS =
            new LinkedHashMap<>();

    static {
        MEMBERS.put(DOOR, names("transport", "direction", "method", "before",
                "after", "faults", "result", "sites", "why"));
        MEMBERS.put(CONFIG_SOURCE, names("method", "keyArg", "defaultArg"));
        MEMBERS.put(CONFIG_FIELD_OWNER, names("class"));
        MEMBERS.put(CODEC, names("codec", "classes"));
        MEMBERS.put(MESSAGE, names("classes", "why"));
        MEMBERS.put(HOOK, names("transport", "direction", "door", "method",
                "before", "after"));
        MEMBERS.put(PUBLISHED_VIEW, names("transport", "path"));
    }

    private static final Pattern NAME = Pattern.compile("[A-Z][A-Z0-9_]*");
    private static final Pattern SIGNATURE = Pattern.compile(
            "<([^:\\s]+): \\S+ ([^(\\s]+)\\(([^)]*)\\)>");
    private static final Pattern CLASS =
            Pattern.compile("[A-Za-z_$][\\w$]*(\\.[A-Za-z_$][\\w$]*)+");

    private static volatile Contents shipped;
    private static volatile List<Door> doors;

    private LibraryCatalog() {
    }

    static final class Contents {
        final List<Door> doors;
        final List<ConfigSource> configSources;
        final Set<String> configFieldOwners;
        final List<Pattern> codecClasses;
        final Set<String> messageClasses;

        private Contents(List<Door> doors, List<ConfigSource> configSources,
                         Set<String> configFieldOwners,
                         List<Pattern> codecClasses,
                         Set<String> messageClasses) {
            this.doors = Collections.unmodifiableList(doors);
            this.configSources = Collections.unmodifiableList(configSources);
            this.configFieldOwners =
                    Collections.unmodifiableSet(configFieldOwners);
            this.codecClasses = Collections.unmodifiableList(codecClasses);
            this.messageClasses = Collections.unmodifiableSet(messageClasses);
        }
    }

    public static final class ConfigSource {
        public final String method;
        public final int keyArg;
        public final int defaultArg;

        private ConfigSource(String method, int keyArg, int defaultArg) {
            this.method = method;
            this.keyArg = keyArg;
            this.defaultArg = defaultArg;
        }
    }

    public enum Result { NONE, FALSE, NULL, ZERO }

    public static final class Door {
        public final String transport;
        public final String direction;
        public final String method;
        public final String anchor;
        public final boolean after;
        public final List<String> faults;
        public final boolean demanded;
        public final boolean dataFlow;
        public final Result result;
        public final String relocated;

        private Door(String transport, String direction, String method,
                     String anchor, boolean after, List<String> faults,
                     boolean demanded, boolean dataFlow, Result result,
                     String relocated) {
            this.transport = transport;
            this.direction = direction;
            this.method = method;
            this.anchor = anchor;
            this.after = after;
            this.faults = Collections.unmodifiableList(faults);
            this.demanded = demanded;
            this.dataFlow = dataFlow;
            this.result = result;
            this.relocated = relocated;
        }

        public String name() {
            return "FAULT:" + transport + ":" + direction;
        }

        public boolean atCalls() {
            return method == null;
        }

        public String family() {
            String owner = owner(method);
            int nested = owner.indexOf('$');
            return nested < 0 ? owner : owner.substring(0, nested);
        }

        String doorMethod() {
            Matcher member = SIGNATURE.matcher(method);
            member.matches();
            return name() + " at " + member.group(1) + "#" + member.group(2);
        }

        String place() {
            return demanded ? "the demanded calls of " + anchor
                    : atCalls() ? "every call of " + anchor : method;
        }
    }

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

    public static List<Door> placedDoors(Path system) throws IOException {
        try (BufferedReader reader = Files.newBufferedReader(system,
                StandardCharsets.UTF_8)) {
            return placed(shipped().doors, hooks(rows(reader,
                    system.getFileName().toString())));
        }
    }

    private static volatile Object[] publishedViews;

    public static boolean publishedView(String transport, String path) {
        String system = System.getProperty(SYSTEM_DOORS, "").trim();
        Object[] known = publishedViews;
        if (known == null || !system.equals(known[0])) {
            List<String[]> views = new ArrayList<>();
            if (!system.isEmpty()) {
                Path file = Paths.get(system);
                try (BufferedReader reader = Files.newBufferedReader(file,
                        StandardCharsets.UTF_8)) {
                    for (Map.Entry<String, JsonObject> entry : rows(reader,
                            file.getFileName().toString()).entrySet()) {
                        JsonObject row = entry.getValue();
                        if (!PUBLISHED_VIEW.equals(kind(row))) continue;
                        try {
                            views.add(new String[] {matching(NAME, text(row,
                                    "transport"), "transport").group(),
                                    text(row, "path")});
                        } catch (RuntimeException malformed) {
                            throw refused(entry.getKey(),
                                    malformed.getMessage(), malformed);
                        }
                    }
                } catch (IOException unreadable) {
                    throw new UncheckedIOException(unreadable);
                }
            }
            known = new Object[] {system, views};
            publishedViews = known;
        }
        @SuppressWarnings("unchecked")
        List<String[]> views = (List<String[]>) known[1];
        for (String[] view : views) {
            if (view[0].equals(transport) && Pattern.matches(
                    Pattern.quote(view[1]).replace("*", "\\E[^/]+\\Q"),
                    path)) {
                return true;
            }
        }
        return false;
    }

    public static List<ConfigSource> configSources() {
        return shipped().configSources;
    }

    public static Set<String> configFieldOwners() {
        return shipped().configFieldOwners;
    }

    public static List<Pattern> codecClasses() {
        return shipped().codecClasses;
    }

    public static Set<String> messageClasses() {
        return shipped().messageClasses;
    }

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

    static final class Hook {
        final String transport;
        final String direction;
        final String door;
        final String method;
        final String anchor;
        final boolean after;

        private Hook(String transport, String direction, String door,
                     String method, String anchor, boolean after) {
            this.transport = transport;
            this.direction = direction;
            this.door = door;
            this.method = method;
            this.anchor = anchor;
            this.after = after;
        }

        boolean places(Door catalog) {
            return catalog.transport.equals(transport)
                    && catalog.direction.equals(direction)
                    && door.equals(catalog.method);
        }
    }

    static List<Door> placed(List<Door> catalog, List<Hook> hooks) {
        List<Door> doors = new ArrayList<>();
        Set<Hook> used = new LinkedHashSet<>();
        for (Door door : catalog) {
            Door placed = door;
            for (Hook hook : hooks) {
                if (!hook.places(door)) continue;
                placed = new Door(door.transport, door.direction,
                        hook.method, hook.anchor, hook.after, door.faults,
                        door.demanded, door.dataFlow, door.result,
                        door.method);
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

    static List<Hook> hooks(Map<String, JsonObject> rows) {
        List<Hook> hooks = new ArrayList<>();
        for (Map.Entry<String, JsonObject> entry : rows.entrySet()) {
            try {
                JsonObject row = entry.getValue();
                if (PUBLISHED_VIEW.equals(kind(row))) continue;
                if (!HOOK.equals(kind(row))) {
                    throw new IllegalArgumentException("a system states "
                            + "where its hooks are (HOOK), never a door");
                }
                String after = optionalText(row, "after");
                if ((after == null) == (optionalText(row, "before") == null)) {
                    throw new IllegalArgumentException(
                            "a hook states one of before and after");
                }
                hooks.add(new Hook(matching(NAME, text(row, "transport"),
                        "transport").group(), matching(NAME, text(row,
                        "direction"), "direction").group(),
                        signature(text(row, "door")).group(),
                        signature(text(row, "method")).group(),
                        signature(after != null ? after
                                : text(row, "before")).group(),
                        after != null));
            } catch (RuntimeException malformed) {
                throw refused(entry.getKey(), malformed.getMessage(),
                        malformed);
            }
        }
        return hooks;
    }

    public static boolean rootsNothing(String name) {
        return doorMarker(name, true) || dataFlowMarker(name);
    }

    public static boolean dataFlowMarker(String name) {
        String[] parts = name == null ? new String[0] : name.split(":", -1);
        if (parts.length < 3 || !"FAULT".equals(parts[0])) return false;
        for (Door door : doors()) {
            if (door.dataFlow && door.transport.equals(parts[1])
                    && door.direction.equals(parts[2])) {
                return true;
            }
        }
        return false;
    }

    public static boolean exchangeMarker(String name) {
        return doorMarker(name, false);
    }

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

    public static Door demandedDoor(String callee) {
        for (Door door : doors()) {
            if (door.demanded && door.anchor.equals(callee)) return door;
        }
        return null;
    }

    public static Set<String> transports() {
        Set<String> found = new LinkedHashSet<>();
        for (Door door : doors()) found.add(door.transport);
        return found;
    }

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

    static Contents read(Map<String, JsonObject> rows) {
        List<Door> doors = new ArrayList<>();
        List<ConfigSource> configSources = new ArrayList<>();
        Set<String> owners = new LinkedHashSet<>();
        List<Pattern> codecs = new ArrayList<>();
        Set<String> messages = new LinkedHashSet<>();
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
                } else if (CODEC.equals(kind)) {
                    identity = CODEC + " " + matching(NAME, text(row,
                            "codec"), "codec").group();
                    JsonElement globs = row.get("classes");
                    if (globs == null || !globs.isJsonArray()
                            || globs.getAsJsonArray().size() == 0) {
                        throw new IllegalArgumentException(
                                "classes lists the codec's class globs");
                    }
                    for (JsonElement glob : globs.getAsJsonArray()) {
                        codecs.add(Pattern.compile(Pattern.quote(
                                string(glob, "classes"))
                                .replace("*", "\\E.*\\Q")));
                    }
                } else if (MESSAGE.equals(kind)) {
                    JsonElement listed = row.get("classes");
                    if (listed == null || !listed.isJsonArray()
                            || listed.getAsJsonArray().size() == 0) {
                        throw new IllegalArgumentException(
                                "classes lists the message classes");
                    }
                    List<String> named = new ArrayList<>();
                    for (JsonElement type : listed.getAsJsonArray()) {
                        named.add(matching(CLASS, string(type, "classes"),
                                "classes").group());
                    }
                    messages.addAll(named);
                    identity = MESSAGE + " " + named;
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
        return new Contents(doors, configSources, owners, codecs, messages);
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
        boolean demanded = DEMANDED.equals(sites);
        boolean dataFlow = DATA_FLOW.equals(sites);
        if (sites != null && !demanded && !dataFlow) {
            throw new IllegalArgumentException("sites is " + DEMANDED
                    + " or " + DATA_FLOW + ": " + sites);
        }
        if (demanded && (method != null || before == null)) {
            throw new IllegalArgumentException("sites " + DEMANDED
                    + " is a door at calls with no method, before its call:"
                    + " a failed operation never happens");
        }
        if (dataFlow && (method == null || before == null)) {
            throw new IllegalArgumentException("sites " + DATA_FLOW
                    + " is a door at a method, before its request: a read"
                    + " that fails never reaches the server");
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
                after != null, faults, demanded, dataFlow, result, null);
    }

    private static Result result(JsonElement value, boolean stated) {
        if (!stated) return Result.NONE;
        if (value.isJsonNull()) return Result.NULL;
        if (value.isJsonPrimitive() && value.getAsJsonPrimitive().isBoolean()
                && !value.getAsBoolean()) {
            return Result.FALSE;
        }
        if (value.isJsonPrimitive() && value.getAsJsonPrimitive().isNumber()
                && "0".equals(value.getAsString())) {
            return Result.ZERO;
        }
        throw new IllegalArgumentException("result is false, null or 0: "
                + value);
    }

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
