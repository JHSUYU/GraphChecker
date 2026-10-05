package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.IOException;
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
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * CONTRACT-SPEC §6: how values cross processes at serialization boundaries,
 * as declared.  One schema for the engine's library catalog and a system's
 * {@code wire.jsonl}, read together: {@code CODEC} (a serialization format,
 * its encoders and decoders), {@code CODEC_VIEW} (how a TREE codec sees an
 * application object), {@code TRANSPORT} (the codecs a door walks its payload with) and
 * {@code EXCHANGE} (a bracket that owns the encodes inside it).  A malformed
 * row, a member its kind does not have, a declaration stated twice and a
 * name no row declares are refused, never skipped: a skipped declaration
 * reads as "never sent".
 */
public final class WireDeclarations {
    public static final int SCHEMA_VERSION = 1;
    public static final String CODEC = "CODEC";
    public static final String CODEC_VIEW = "CODEC_VIEW";
    public static final String TRANSPORT = "TRANSPORT";
    public static final String EXCHANGE = "EXCHANGE";
    /** A view's codec that names every TREE codec. */
    public static final String EVERY_CODEC = "*";

    /** What a codec's walker walks: containers, generated messages, or
     *  the graph as one leaf. */
    public enum Shape { TREE, PROTOBUF, LEAF }

    /** What an object's view is: its map, one leaf, or a flat name/value
     *  list. */
    public enum ViewForm { MAP, LEAF, PAIRS }

    private static final Map<String, Set<String>> MEMBERS =
            new LinkedHashMap<>();
    private static final Set<String> ENCODER =
            names("method", "call", "graph", "encoded", "bind");
    private static final Set<String> DECODER =
            names("method", "call", "graph", "encoded");

    static {
        MEMBERS.put(CODEC, names("codec", "shape", "space", "encoders",
                "decoders"));
        MEMBERS.put(CODEC_VIEW, names("codec", "type", "map", "leaf", "pairs",
                "put"));
        MEMBERS.put(TRANSPORT, names("transport", "request", "response",
                "store", "envelopeBytes"));
        MEMBERS.put(EXCHANGE, names("transport", "method"));
    }

    /** A codec or transport name. */
    private static final Pattern NAME = Pattern.compile("[A-Z][A-Z0-9_]*");
    /** A key space: it names no {@code :}, so a port name reads back. */
    private static final Pattern SPACE = Pattern.compile("[a-z][a-z0-9_]*");
    /** A Soot method signature; in a {@code call} pattern {@code *} is any
     *  run of characters. */
    private static final Pattern SIGNATURE =
            Pattern.compile("<[^:\\s]+: \\S+ \\S+\\([^)]*\\)>");
    /** Where a hook finds a value: the receiver, the result, an argument. */
    private static final Pattern SLOT =
            Pattern.compile("this|return|arg(0|[1-9][0-9]*)");
    /** A view's accessor: a no-argument method or a field. */
    private static final Pattern ACCESSOR =
            Pattern.compile("[A-Za-z_$][A-Za-z0-9_$]*(\\(\\))?");
    private static final Pattern INDEX = Pattern.compile("0|[1-9][0-9]*");

    private final List<Codec> codecs;
    private final List<View> views;
    private final List<Transport> transports;
    private final List<Exchange> exchanges;

    private WireDeclarations(List<Codec> codecs, List<View> views,
                             List<Transport> transports,
                             List<Exchange> exchanges) {
        this.codecs = Collections.unmodifiableList(codecs);
        this.views = Collections.unmodifiableList(views);
        this.transports = Collections.unmodifiableList(transports);
        this.exchanges = Collections.unmodifiableList(exchanges);
    }

    /**
     * Every declaration of the rows, each keyed by where it was read
     * ({@code file:line}); a row of another kind is the caller's to route
     * away first.  Refuses, naming the row, what the schema does not accept.
     */
    public static WireDeclarations of(Map<String, JsonObject> rows) {
        List<Codec> codecs = new ArrayList<>();
        List<View> views = new ArrayList<>();
        List<Transport> transports = new ArrayList<>();
        List<Exchange> exchanges = new ArrayList<>();
        Map<String, String> declaredAt = new LinkedHashMap<>();
        Map<Value, String> located = new LinkedHashMap<>();
        for (Map.Entry<String, JsonObject> entry : rows.entrySet()) {
            try {
                JsonObject row = Fields.required(entry.getValue(), "row");
                Value declared;
                String identity;
                switch (kind(row)) {
                    case CODEC:
                        Codec codec = codec(row);
                        codecs.add(codec);
                        declared = codec;
                        identity = CODEC + " " + codec.name();
                        break;
                    case CODEC_VIEW:
                        View view = view(row);
                        views.add(view);
                        declared = view;
                        identity = CODEC_VIEW + " " + view.codec() + " "
                                + view.type();
                        break;
                    case TRANSPORT:
                        Transport transport = transport(row);
                        transports.add(transport);
                        declared = transport;
                        identity = TRANSPORT + " " + transport.name();
                        break;
                    default:
                        Exchange exchange = new Exchange(
                                name(text(row, "transport"), "transport"),
                                signature(text(row, "method"), false));
                        exchanges.add(exchange);
                        declared = exchange;
                        identity = EXCHANGE + " " + exchange.method();
                        break;
                }
                String first = declaredAt.putIfAbsent(identity,
                        entry.getKey());
                if (first != null) {
                    throw new IllegalArgumentException(identity
                            + " is declared again; first at " + first);
                }
                located.put(declared, entry.getKey());
            } catch (RuntimeException malformed) {
                throw refused(entry.getKey(), malformed.getMessage(),
                        malformed);
            }
        }
        WireDeclarations read = new WireDeclarations(codecs, views,
                transports, exchanges);
        read.resolve(located);
        return read;
    }

    /**
     * The declarations of one file, one JSON row per line, keyed
     * {@code file:line}.  A {@code DOOR} row is the door weave's
     * ({@code causynth.DoorWeave}) and is passed over; any other row is one of
     * the four kinds or refused.
     */
    public static WireDeclarations read(Path file) throws IOException {
        Map<String, JsonObject> rows = new LinkedHashMap<>();
        int line = 0;
        for (String text : Files.readAllLines(file, StandardCharsets.UTF_8)) {
            line++;
            if (text.trim().isEmpty()) continue;
            String at = file + ":" + line;
            JsonElement parsed;
            try {
                parsed = JsonParser.parseString(text);
            } catch (RuntimeException malformed) {
                throw refused(at, "not JSON: " + malformed.getMessage(),
                        malformed);
            }
            if (!parsed.isJsonObject()) {
                throw refused(at, "a row is a JSON object", null);
            }
            JsonElement kind = parsed.getAsJsonObject().get("kind");
            if (kind != null && kind.isJsonPrimitive()
                    && DOOR.equals(kind.getAsString())) continue;
            rows.put(at, parsed.getAsJsonObject());
        }
        return of(rows);
    }

    /**
     * The declarations this JVM was given ({@link #PROPERTY}, else
     * {@link #ENVIRONMENT}): the weave that hooks the codecs and the replay
     * that runs them read the same file.  None when neither names one: the
     * system declares no codec.
     */
    public static WireDeclarations configured() throws IOException {
        String named = System.getProperty(PROPERTY);
        if (named == null || named.trim().isEmpty()) {
            named = System.getenv(ENVIRONMENT);
        }
        if (named == null || named.trim().isEmpty()) return NONE;
        Path file = Paths.get(named.trim()).toAbsolutePath().normalize();
        if (!Files.isRegularFile(file)) {
            throw new IOException("wire declarations not found: " + file);
        }
        return read(file);
    }

    /** The system property naming the declarations file. */
    public static final String PROPERTY = "causynth.wire.declarations";
    /** The environment variable naming it when the property does not. */
    public static final String ENVIRONMENT = "CAUSYNTH_WIRE_DECLARATIONS";
    /**
     * The header bound of a request/response transport that states none:
     * half of Jetty's 8 KB request-header default, so the trace header and
     * the transport's own fit beside it.
     */
    public static final int DEFAULT_ENVELOPE_BYTES = 4096;
    /** A row kind this schema leaves to the door weave. */
    private static final String DOOR = "DOOR";
    /** No declaration at all. */
    public static final WireDeclarations NONE = new WireDeclarations(
            new ArrayList<Codec>(), new ArrayList<View>(),
            new ArrayList<Transport>(), new ArrayList<Exchange>());

    /** Every name a row uses is declared, by a row of the right kind. */
    private void resolve(Map<Value, String> located) {
        for (View view : views) {
            if (EVERY_CODEC.equals(view.codec())) continue;
            Codec codec = codec(view.codec());
            if (codec != null && codec.shape() == Shape.TREE) continue;
            throw refused(located.get(view), "a view is a TREE codec's, and "
                    + "no TREE codec is named " + view.codec(), null);
        }
        Set<String> named = new LinkedHashSet<>();
        for (Transport transport : transports) {
            named.add(transport.name());
            for (String walked : Arrays.asList(transport.request(),
                    transport.response())) {
                if (walked == null || codec(walked) != null) continue;
                throw refused(located.get(transport), "the transport walks "
                        + "its payload with " + walked + ", which no " + CODEC
                        + " row declares", null);
            }
        }
        for (Exchange exchange : exchanges) {
            if (named.contains(exchange.transport())) continue;
            throw refused(located.get(exchange), "the exchange names "
                    + "transport " + exchange.transport() + ", which no "
                    + TRANSPORT + " row declares", null);
        }
    }

    private static IllegalArgumentException refused(String at, String why,
                                                    Throwable cause) {
        return new IllegalArgumentException("wire declaration at " + at
                + ": " + why, cause);
    }

    public List<Codec> codecs() {
        return codecs;
    }

    /** The codec of that name, or null. */
    public Codec codec(String name) {
        for (Codec codec : codecs) {
            if (codec.name().equals(name)) return codec;
        }
        return null;
    }

    public List<View> views() {
        return views;
    }

    public List<Transport> transports() {
        return transports;
    }

    /** The transport of that name, or null. */
    public Transport transport(String name) {
        for (Transport transport : transports) {
            if (transport.name().equals(name)) return transport;
        }
        return null;
    }

    public List<Exchange> exchanges() {
        return exchanges;
    }

    // ---- one parser per kind -------------------------------------------

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
        members(row, members, kind);
        return kind;
    }

    private static Codec codec(JsonObject row) {
        List<Hook> decoders = hooks(row, "decoders", false);
        if (decoders.isEmpty()) {
            throw new IllegalArgumentException(
                    "a codec states its decoders; with none it mints nothing");
        }
        return new Codec(name(text(row, "codec"), "codec"),
                constant(Shape.class, text(row, "shape"), "shape"),
                space(row), hooks(row, "encoders", true), decoders);
    }

    private static List<Hook> hooks(JsonObject row, String member,
                                    boolean encoder) {
        List<Hook> hooks = new ArrayList<>();
        JsonElement listed = row.get(member);
        if (listed == null) return hooks;
        if (!listed.isJsonArray()) {
            throw new IllegalArgumentException(member + " is a list");
        }
        for (JsonElement element : listed.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(member
                        + " lists objects; got " + element);
            }
            hooks.add(hook(element.getAsJsonObject(), member, encoder));
        }
        return hooks;
    }

    private static Hook hook(JsonObject row, String member, boolean encoder) {
        members(row, encoder ? ENCODER : DECODER, member + " entry");
        String method = optionalText(row, "method");
        String call = optionalText(row, "call");
        if ((method == null) == (call == null)) {
            throw new IllegalArgumentException(member
                    + " entry states one of method and call: " + row);
        }
        String graph = slot(text(row, "graph"), "graph");
        String encoded = optionalText(row, "encoded");
        if (encoded != null && slot(encoded, "encoded").equals(graph)) {
            throw new IllegalArgumentException(member + " entry's graph and "
                    + "encoded are one slot: " + graph);
        }
        String bind = optionalText(row, "bind");
        if (bind != null && !EXCHANGE.equals(bind)) {
            throw new IllegalArgumentException(
                    "an encoder binds to an EXCHANGE or to its encoded "
                            + "object; got bind " + bind);
        }
        if (encoder && bind == null && encoded == null) {
            throw new IllegalArgumentException("an encoder bound to its "
                    + "encoded object states which one: " + row);
        }
        return new Hook(signature(method != null ? method : call,
                method == null), method == null, graph, encoded,
                bind != null);
    }

    private static View view(JsonObject row) {
        String codec = text(row, "codec");
        if (!EVERY_CODEC.equals(codec)) name(codec, "codec");
        String type = text(row, "type");
        if (type.matches(".*\\s.*")) {
            throw new IllegalArgumentException("type is a class name: " + type);
        }
        ViewForm form = null;
        String accessor = null;
        for (ViewForm candidate : ViewForm.values()) {
            String stated = optionalText(row, member(candidate));
            if (stated == null) continue;
            if (form != null) {
                throw new IllegalArgumentException(
                        "a view is one of map, leaf and pairs, not "
                                + member(form) + " and " + member(candidate));
            }
            form = candidate;
            accessor = accessor(stated);
        }
        if (form == null) {
            throw new IllegalArgumentException(
                    "a view states one of map, leaf and pairs");
        }
        Map<String, String> put = new LinkedHashMap<>();
        JsonElement extra = row.get("put");
        if (extra != null) {
            if (form != ViewForm.MAP || !extra.isJsonObject()) {
                throw new IllegalArgumentException("put is an object of "
                        + "extra keys, beside a map view only");
            }
            for (Map.Entry<String, JsonElement> key
                    : extra.getAsJsonObject().entrySet()) {
                put.put(key.getKey(), accessor(string(key.getValue(),
                        "put." + key.getKey())));
            }
        }
        return new View(codec, type, form, accessor, put);
    }

    private static Transport transport(JsonObject row) {
        String request = optionalText(row, "request");
        String response = optionalText(row, "response");
        JsonElement store = row.get("store");
        if (store != null && (!store.isJsonPrimitive()
                || !store.getAsJsonPrimitive().isBoolean())) {
            throw new IllegalArgumentException("store is a boolean");
        }
        boolean stored = store != null && store.getAsBoolean();
        if (stored ? request != null || response != null
                : request == null && response == null) {
            throw new IllegalArgumentException("a transport is a store, or "
                    + "walks a request or a response with a codec: one of "
                    + "the two");
        }
        int bytes = index(row, "envelopeBytes");
        if (bytes == 0 || bytes > 0 && stored) {
            throw new IllegalArgumentException("envelopeBytes bounds the "
                    + "header a message's envelope travels in: a positive "
                    + "count, beside a request or a response");
        }
        return new Transport(name(text(row, "transport"), "transport"),
                request == null ? null : name(request, "request"),
                response == null ? null : name(response, "response"), stored,
                stored ? 0 : bytes < 0 ? DEFAULT_ENVELOPE_BYTES : bytes);
    }

    // ---- members ---------------------------------------------------------

    private static Set<String> names(String... names) {
        Set<String> set = new LinkedHashSet<>(Arrays.asList(names));
        set.add("schemaVersion");
        set.add("kind");
        return set;
    }

    private static void members(JsonObject row, Set<String> allowed,
                                String what) {
        for (String member : row.keySet()) {
            if (!allowed.contains(member)) {
                throw new IllegalArgumentException(what + " has no member "
                        + member);
            }
        }
    }

    private static String text(JsonObject row, String member) {
        String stated = optionalText(row, member);
        if (stated == null) {
            throw new IllegalArgumentException("states no " + member);
        }
        return stated;
    }

    /** A string member, or null when absent; blank is refused. */
    private static String optionalText(JsonObject row, String member) {
        JsonElement value = row.get(member);
        if (value == null) return null;
        String stated = string(value, member).trim();
        if (stated.isEmpty()) {
            throw new IllegalArgumentException(member + " is blank");
        }
        return stated;
    }

    private static String string(JsonElement value, String member) {
        if (!value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isString()) {
            throw new IllegalArgumentException(member + " is not a string: "
                    + value);
        }
        return value.getAsString();
    }

    /** An argument index, or -1 when absent. */
    private static int index(JsonObject row, String member) {
        JsonElement value = row.get(member);
        if (value == null) return -1;
        if (!value.isJsonPrimitive() || !value.getAsJsonPrimitive().isNumber()
                || !INDEX.matcher(value.getAsString()).matches()) {
            throw new IllegalArgumentException(member
                    + " is an argument index; got " + value);
        }
        return Integer.parseInt(value.getAsString());
    }

    private static String name(String name, String member) {
        return matching(NAME, name, member);
    }

    private static String space(JsonObject row) {
        return matching(SPACE, text(row, "space"), "space");
    }

    private static String slot(String slot, String member) {
        return matching(SLOT, slot, member);
    }

    private static String accessor(String accessor) {
        return matching(ACCESSOR, accessor, "accessor");
    }

    /** A signature; {@code *} only in a pattern. */
    private static String signature(String signature, boolean pattern) {
        matching(SIGNATURE, signature, pattern ? "call" : "method");
        if (!pattern && signature.indexOf('*') >= 0) {
            throw new IllegalArgumentException("method names one method; "
                    + "a pattern is a call: " + signature);
        }
        return signature;
    }

    private static String matching(Pattern pattern, String value,
                                   String member) {
        if (!pattern.matcher(value).matches()) {
            throw new IllegalArgumentException(member + " " + value
                    + " is not " + pattern.pattern());
        }
        return value;
    }

    private static <E extends Enum<E>> E constant(Class<E> type, String name,
                                                  String member) {
        try {
            return Enum.valueOf(type, name);
        } catch (IllegalArgumentException unknown) {
            throw new IllegalArgumentException(member + " " + name
                    + " is none of " + Arrays.toString(
                    type.getEnumConstants()));
        }
    }

    private static String member(ViewForm form) {
        return form.name().toLowerCase(Locale.ROOT);
    }

    // ---- the declarations -------------------------------------------------

    /** One serialization format. */
    public static final class Codec extends Value {
        private final String name;
        private final Shape shape;
        private final String space;
        private final List<Hook> encoders;
        private final List<Hook> decoders;

        private Codec(String name, Shape shape, String space,
                      List<Hook> encoders, List<Hook> decoders) {
            this.name = name;
            this.shape = shape;
            this.space = space;
            this.encoders = Collections.unmodifiableList(encoders);
            this.decoders = Collections.unmodifiableList(decoders);
        }

        public String name() {
            return name;
        }

        public Shape shape() {
            return shape;
        }

        /** The key space its ports are named in. */
        public String space() {
            return space;
        }

        /** None when its payloads are walked at the door. */
        public List<Hook> encoders() {
            return encoders;
        }

        public List<Hook> decoders() {
            return decoders;
        }

        @Override
        Object[] parts() {
            return new Object[] {name, shape, space, encoders, decoders};
        }

        @Override
        public String toString() {
            return CODEC + " " + name;
        }
    }

    /**
     * One encoder or decoder: a method whose body is hooked, or a
     * {@code call} pattern whose call sites in woven code are; {@code graph}
     * is where the object graph is, {@code encoded} where its encoded form
     * is ({@code this}, {@code return} or {@code argN}).  A decoder whose
     * graph is an argument is hooked at entry.  An encoder is bound to its
     * encoded object, or to the innermost open EXCHANGE bracket.
     */
    public static final class Hook extends Value {
        private final String target;
        private final boolean call;
        private final String graph;
        private final String encoded;
        private final boolean exchange;

        private Hook(String target, boolean call, String graph,
                     String encoded, boolean exchange) {
            this.target = target;
            this.call = call;
            this.graph = graph;
            this.encoded = encoded;
            this.exchange = exchange;
        }

        /** The method's signature, or the callee pattern of a call hook. */
        public String target() {
            return target;
        }

        public boolean call() {
            return call;
        }

        public String graph() {
            return graph;
        }

        /** Where the encoded form is, or null when the hook states none. */
        public String encoded() {
            return encoded;
        }

        /** Whether an encoder is bound to its EXCHANGE bracket. */
        public boolean exchange() {
            return exchange;
        }

        /** Whether a call of {@code callee} is this call hook's: its
         *  pattern with {@code *} as any run of characters. */
        public boolean calls(String callee) {
            if (!call) return false;
            StringBuilder regex = new StringBuilder();
            for (String piece : target.split("\\*", -1)) {
                if (regex.length() > 0) regex.append(".*");
                regex.append(Pattern.quote(piece));
            }
            return callee.matches(regex.toString());
        }

        @Override
        Object[] parts() {
            return new Object[] {target, call, graph, encoded, exchange};
        }

        @Override
        public String toString() {
            return (call ? "call " : "") + target;
        }
    }

    /** How a TREE codec sees one application type (the most specific type
     *  wins); it returns the object's own containers, never a copy. */
    public static final class View extends Value {
        private final String codec;
        private final String type;
        private final ViewForm form;
        private final String accessor;
        private final Map<String, String> put;

        private View(String codec, String type, ViewForm form,
                     String accessor, Map<String, String> put) {
            this.codec = codec;
            this.type = type;
            this.form = form;
            this.accessor = accessor;
            this.put = Collections.unmodifiableMap(put);
        }

        /** The codec, or {@link #EVERY_CODEC}. */
        public String codec() {
            return codec;
        }

        public String type() {
            return type;
        }

        public ViewForm form() {
            return form;
        }

        /** {@code name()} (a method) or {@code name} (a field). */
        public String accessor() {
            return accessor;
        }

        /** The extra keys a map view writes, key to accessor. */
        public Map<String, String> put() {
            return put;
        }

        @Override
        Object[] parts() {
            return new Object[] {codec, type, form, accessor, put};
        }

        @Override
        public String toString() {
            return CODEC_VIEW + " " + codec + " " + type;
        }
    }

    /** The codecs a transport's doors walk their payloads with (null: that
     *  half has no payload in hand), or a store's; and the most bytes a
     *  message's symbolic header may take ({@link #DEFAULT_ENVELOPE_BYTES}
     *  unless stated; 0 for a store, whose versions travel in no header). */
    public static final class Transport extends Value {
        private final String name;
        private final String request;
        private final String response;
        private final boolean store;
        private final int envelopeBytes;

        private Transport(String name, String request, String response,
                          boolean store, int envelopeBytes) {
            this.name = name;
            this.request = request;
            this.response = response;
            this.store = store;
            this.envelopeBytes = envelopeBytes;
        }

        public String name() {
            return name;
        }

        public String request() {
            return request;
        }

        public String response() {
            return response;
        }

        /** The codec one half's door walks its payload with, or null. */
        public String codec(boolean requestHalf) {
            return requestHalf ? request : response;
        }

        /** Whether its doors write and read stored versions. */
        public boolean store() {
            return store;
        }

        /** The symbolic header's byte bound, 0 for a store. */
        public int envelopeBytes() {
            return envelopeBytes;
        }

        @Override
        Object[] parts() {
            return new Object[] {name, request, response, store,
                    envelopeBytes};
        }

        @Override
        public String toString() {
            return TRANSPORT + " " + name;
        }
    }

    /** A woven bracket of one transport: the encodes inside it are staged
     *  on it, and its transport's next outbound door drains them. */
    public static final class Exchange extends Value {
        private final String transport;
        private final String method;

        private Exchange(String transport, String method) {
            this.transport = transport;
            this.method = method;
        }

        public String transport() {
            return transport;
        }

        public String method() {
            return method;
        }

        @Override
        Object[] parts() {
            return new Object[] {transport, method};
        }

        @Override
        public String toString() {
            return EXCHANGE + " " + method;
        }
    }
}
