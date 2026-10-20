package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class RecordingPlant {
    static final String PROPERTY = "causynth.plant";
    static final String APPLIED = "PLANT_APPLIED";
    static final String HOLDING = "PLANT_HOLDING";
    static final String UNHELD = "PLANT_UNHELD";
    static final String LATE = "PLANT_LATE";
    static final String OBSERVED = "PLANT_OBSERVED";
    static final String UNWRITTEN = "PLANT_UNWRITTEN";
    static final String FATAL = "PLANT_FATAL";
    public static final String ROOT = "ROOT";
    public static final String ORDER = "ORDER";
    public static final String VIEW_HOLD = "VIEW_HOLD";
    public static final String SCOPE = "scope";
    public static final String CHECK = "check";
    public static final String TARGET = "TARGET";
    public static final String CLOCK_SITE = "CLOCK_SITE";
    public static final String ANSWER = "ANSWER";
    public static final String KIND = "kind";
    public static final String ROW = "row";
    public static final String CATEGORY = "category";
    public static final String ROOT_ID = "rootId";
    public static final String OCCURRENCE = "occurrence";
    public static final String SITE = "siteId";
    public static final String INVOCATION = "invocation";
    public static final String SITES = "sites";
    public static final String CALLEE = "callee";
    public static final String JAVA_TYPE = "javaType";
    public static final String VALUE = "value";
    public static final String SKEW = "skew";
    public static final String CLOCK = "clock";
    public static final String NANOS = "nanos";
    public static final String SOURCE = "source";
    public static final String REGIONS = "regions";
    public static final String ENDPOINT = "endpoint";
    public static final String PORT = "port";

    private static final boolean PLANTING = !file().isEmpty();
    private static volatile Plant plant;
    private static final AtomicBoolean ENDED = new AtomicBoolean();
    private static final AtomicLong PLACES = new AtomicLong();
    private static final Set<String> CLOCKED = ConcurrentHashMap.newKeySet();
    private static final Set<Integer> STATED = ConcurrentHashMap.newKeySet();
    private static volatile boolean gaveWay;
    private static final Map<String, Integer> INVOCATIONS =
            new ConcurrentHashMap<String, Integer>();
    private static final ThreadLocal<Object[]> ANSWERED =
            new ThreadLocal<Object[]>();

    private RecordingPlant() {
    }

    static void gaveWay() {
        gaveWay = true;
    }

    static boolean orderGaveWay() {
        return gaveWay;
    }

    static boolean planting() {
        return PLANTING;
    }

    public static boolean checked(JsonObject order) {
        JsonElement check = order.get(CHECK);
        return check != null && check.isJsonPrimitive()
                && check.getAsBoolean();
    }

    static String file() {
        return System.getProperty(PROPERTY, "").trim();
    }

    static final class Root {
        final int row;
        final String value;

        Root(int row, String value) {
            this.row = row;
            this.value = value;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Root && ((Root) other).row == row
                    && ((Root) other).value.equals(value);
        }

        @Override
        public int hashCode() {
            return 31 * row + value.hashCode();
        }

        @Override
        public String toString() {
            return row + "=" + value;
        }
    }

    static final class Valued {
        final Root root;
        final String rootId;
        final String javaType;

        Valued(Root root, String rootId, String javaType) {
            this.root = root;
            this.rootId = rootId;
            this.javaType = javaType;
        }
    }

    static final class Jump {
        final int row;
        final String rootId;
        final Clock clock;
        final long skew;

        Jump(int row, String rootId, Clock clock, long skew) {
            this.row = row;
            this.rootId = rootId;
            this.clock = clock;
            this.skew = skew;
        }
    }

    static final class Answering {
        final Set<String> regions = new LinkedHashSet<String>();
        final Map<String, Root> endpoints = new LinkedHashMap<String, Root>();
    }

    static final class Call {
        final String callee;
        Clock clock;
        final Set<String> regions = new LinkedHashSet<String>();
        final Map<String, Jump> jumps = new LinkedHashMap<String, Jump>();
        final List<Valued> configs = new ArrayList<Valued>();
        final Map<String, Valued> reads = new LinkedHashMap<String, Valued>();
        final Map<String, Answering> answers =
                new LinkedHashMap<String, Answering>();

        Call(String callee) {
            this.callee = callee;
        }
    }

    static final class Plant {
        final Map<String, Map<String, Map<Integer, Root>>> markers;
        final Map<String, Root> hooks;
        final Map<String, Call> calls;
        final Set<String> focused;
        final Map<String, Boolean> fatalArms;
        final String anchor;

        Plant(Map<String, Map<String, Map<Integer, Root>>> markers,
              Map<String, Root> hooks, Map<String, Call> calls,
              Set<String> focused, Map<String, Boolean> fatalArms,
              String anchor) {
            this.markers = markers;
            this.hooks = hooks;
            this.calls = calls;
            this.focused = focused;
            this.fatalArms = fatalArms;
            this.anchor = anchor;
        }
    }

    static boolean marker(String name) {
        if (!PLANTING || !RecordingWindow.opened()) return false;
        CausynthTraceRecorder.ActiveCallSiteContext site =
                CausynthTraceRecorder.currentCallSiteContext();
        if (site == null) return false;
        Map<String, Map<Integer, Root>> rows =
                plant().markers.get(site.siteId());
        String occurrence = plantedOccurrence(rows,
                CausynthTraceRecorder.enclosingOccurrences());
        if (occurrence == null) return false;
        String id = OccurrenceAddress.parse(occurrence).id();
        int invocation = INVOCATIONS.merge(site.siteId() + "|" + id, 1,
                Integer::sum);
        Root root = rows.get(id).get(invocation);
        if (root == null) return false;
        boolean value = Boolean.parseBoolean(root.value);
        CausynthTraceRecorder.plantRoot(APPLIED, root.row, name, occurrence,
                String.valueOf(value));
        if (value) {
            ANSWERED.set(new Object[] {root, name, occurrence});
            Identity.doorFaulted(name);
        }
        return value;
    }

    static boolean plantRefused(String name, String why) {
        if (!PLANTING) return false;
        Object[] answered = ANSWERED.get();
        ANSWERED.remove();
        if (answered == null || !name.equals(answered[1])) return true;
        CausynthTraceRecorder.plantRoot(UNWRITTEN, ((Root) answered[0]).row,
                name + ": " + why, (String) answered[2], "true");
        return true;
    }

    static void hook(String rootId, Object owner, String fieldSignature) {
        if (!PLANTING || !RecordingWindow.opened()) return;
        Plant rows = plant();
        Root root = rows.hooks.get(rootId);
        if (root == null) return;
        String occurrence = focusedOccurrence(rows.focused,
                CausynthTraceRecorder.enclosingOccurrences());
        if (occurrence == null) return;
        CausynthTraceRecorder.plantRoot(RootMint.writeModeledField(owner,
                fieldSignature, "", root.value) ? APPLIED : UNWRITTEN,
                root.row, rootId, occurrence, root.value);
    }

    public static long returned(long value) {
        if (!PLANTING) return value;
        Object planted = intercept(value);
        return planted instanceof Number ? ((Number) planted).longValue()
                : value;
    }

    public static int returned(int value) {
        if (!PLANTING) return value;
        Object planted = intercept(value);
        return planted instanceof Number ? ((Number) planted).intValue()
                : value;
    }

    public static boolean returned(boolean value) {
        if (!PLANTING) return value;
        Object planted = intercept(value);
        return planted instanceof Boolean ? (Boolean) planted : value;
    }

    public static float returned(float value) {
        if (!PLANTING) return value;
        Object planted = intercept(value);
        return planted instanceof Number ? ((Number) planted).floatValue()
                : value;
    }

    public static double returned(double value) {
        if (!PLANTING) return value;
        Object planted = intercept(value);
        return planted instanceof Number ? ((Number) planted).doubleValue()
                : value;
    }

    public static Object returned(Object value) {
        return PLANTING ? intercept(value) : value;
    }

    private static Object intercept(Object host) {
        if (!RecordingWindow.opened()) return host;
        CausynthTraceRecorder.ActiveCallSiteContext site =
                CausynthTraceRecorder.currentCallSiteContext();
        return site == null ? host : returnedAt(plant(), site.siteId(),
                site.declaredCallee(),
                CausynthTraceRecorder.enclosingOccurrences(), host);
    }

    static Object returnedAt(Plant plant, String siteId, String callee,
                             List<String> enclosing, Object host) {
        Call call = plant.calls.get(siteId);
        if (call == null || !call.callee.equals(callee)) return host;
        String innermost = enclosing.isEmpty() ? "" : enclosing.get(0);
        Object value = host;
        for (Valued config : call.configs) {
            value = valued(config, value, innermost);
        }
        String read = plantedOccurrence(call.reads, enclosing);
        if (read != null) {
            value = valued(call.reads.get(OccurrenceAddress.parse(read).id()),
                    value, read);
        }
        if (call.clock != null || !call.jumps.isEmpty()) {
            value = clocked(call, value, enclosing);
        }
        for (Map.Entry<String, Answering> port : call.answers.entrySet()) {
            value = answered(port.getKey(), port.getValue(), value,
                    enclosing);
        }
        return value;
    }

    private static Object valued(Valued valued, Object host,
                                 String occurrence) {
        Object planted = ModelValues.coerce("", valued.root.value,
                returnedType(host, valued.javaType));
        if (planted == ModelValues.UnsupportedReplayValue.INSTANCE
                || planted == null && host != null
                && returnedType(host, "").isPrimitive()) {
            stateOnce(UNWRITTEN, valued.root.row, valued.rootId, occurrence,
                    valued.root.value);
            return host;
        }
        stateOnce(APPLIED, valued.root.row, valued.rootId, occurrence,
                valued.root.value);
        return planted;
    }

    private static Object clocked(Call call, Object host,
                                  List<String> enclosing) {
        if (!(host instanceof Long || host instanceof Integer)) return host;
        long reading = ((Number) host).longValue();
        long place = PLACES.incrementAndGet();
        String minted = plantedOccurrence(call.jumps, enclosing);
        if (minted != null) {
            OccurrenceAddress mint = OccurrenceAddress.parse(minted);
            Jump jump = call.jumps.get(mint.id());
            if (CLOCKED.add(mint.id() + "|" + jump.rootId)) {
                NodeClocks.jump(mint.node().render(), jump.clock, place,
                        jump.skew);
                long instant = reading + jump.skew;
                stateOnce(APPLIED, jump.row, jump.rootId, minted,
                        Long.toString(instant));
                return box(host, instant);
            }
        }
        String at = declaringOccurrence(call.regions, enclosing);
        if (at == null || call.clock == null) return host;
        long skew = NodeClocks.skew(OccurrenceAddress.parse(at).node()
                .render(), call.clock, place);
        return skew == 0L ? host : box(host, reading + skew);
    }

    private static Object answered(String port, final Answering answering,
                                   Object host, List<String> enclosing) {
        final String at = declaringOccurrence(answering.regions, enclosing);
        if (at == null) return host;
        return HandoffMint.answerNatively(port, host,
                OccurrenceAddress.parse(at), new HandoffMint.NativeAnswers() {
                    @Override
                    public String answer(String endpointId) {
                        Root root = answering.endpoints.get(endpointId);
                        return root == null ? null : root.value;
                    }

                    @Override
                    public void planted(String endpointId, boolean written) {
                        Root root = answering.endpoints.get(endpointId);
                        stateOnce(written ? APPLIED : UNWRITTEN, root.row,
                                endpointId, at, root.value);
                    }
                });
    }

    static Class<?> returnedType(Object host, String javaType) {
        if (host instanceof Long) return long.class;
        if (host instanceof Integer) return int.class;
        if (host instanceof Boolean) return boolean.class;
        if (host instanceof Float) return float.class;
        if (host instanceof Double) return double.class;
        if (host != null) return host.getClass();
        if (javaType == null || javaType.isEmpty()) return Object.class;
        try {
            return Class.forName(javaType, false,
                    Thread.currentThread().getContextClassLoader());
        } catch (ClassNotFoundException | RuntimeException unknown) {
            return Object.class;
        }
    }

    private static Object box(Object host, long instant) {
        return host instanceof Integer ? Integer.valueOf((int) instant)
                : Long.valueOf(instant);
    }

    private static void stateOnce(String event, int row, String planted,
                                  String occurrence, String value) {
        if (STATED.add(row)) {
            CausynthTraceRecorder.plantRoot(event, row, planted, occurrence,
                    value);
        }
    }

    static void ordered(String event, int row, String after,
                        String waitingFor) {
        CausynthTraceRecorder.plantOrdered(event, row, after, waitingFor);
    }

    static void decided(String siteId, Boolean outcome) {
        if (!PLANTING || outcome == null) return;
        Plant rows = plant();
        if (!outcome.equals(rows.fatalArms.get(siteId))
                || !RecordingWindow.opened()) {
            return;
        }
        List<String> enclosing = CausynthTraceRecorder.enclosingOccurrences();
        String anchor = anchorOf(enclosing, rows.anchor);
        CausynthTraceRecorder.plantFatal(siteId, anchor != null ? anchor
                : enclosing.isEmpty() ? "" : enclosing.get(0), anchor != null);
        if (anchor != null && ENDED.compareAndSet(false, true)) {
            end(siteId, anchor);
        }
    }

    static String anchorOf(List<String> enclosing, String anchor) {
        for (String occurrence : enclosing) {
            if (OccurrenceAddress.parse(occurrence).id().equals(anchor)) {
                return occurrence;
            }
        }
        return null;
    }

    static String focusedOccurrence(Set<String> focused,
                                    List<String> enclosing) {
        for (String occurrence : enclosing) {
            if (focused.contains(OccurrenceAddress.parse(occurrence).id())) {
                return occurrence;
            }
        }
        return null;
    }

    static String plantedOccurrence(Map<String, ?> byOccurrence,
                                    List<String> enclosing) {
        if (byOccurrence == null || byOccurrence.isEmpty()) return null;
        for (String occurrence : enclosing) {
            if (byOccurrence.containsKey(
                    OccurrenceAddress.parse(occurrence).id())) {
                return occurrence;
            }
        }
        return null;
    }

    static String declaringOccurrence(Set<String> regions,
                                      List<String> enclosing) {
        for (String occurrence : enclosing) {
            if (regions.contains(OccurrenceAddress.parse(occurrence)
                    .regionId())) {
                return occurrence;
            }
        }
        return null;
    }

    private static void end(final String siteId, final String anchor) {
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        new Thread(root, new Runnable() {
            @Override
            public void run() {
                EngineConsole.println("Causynth " + java.time.Instant.now()
                        + ": the native run ends AT_ANCHOR: the planted world"
                        + " took the fatal arm of " + siteId + " at "
                        + anchor);
                JUnitMethodRunner.exit(0);
            }
        }, "causynth-plant-end").start();
    }

    static Plant plant() {
        Plant rows = plant;
        if (rows != null) return rows;
        synchronized (RecordingPlant.class) {
            if (plant == null) {
                try {
                    plant = read(Paths.get(file()));
                } catch (IOException | RuntimeException unreadable) {
                    throw new IllegalStateException("the plant -D" + PROPERTY
                            + "=" + file() + " is unreadable: "
                            + unreadable.getMessage(), unreadable);
                }
            }
            return plant;
        }
    }

    private static boolean ordered(JsonObject row) {
        if (optionalString(row, SCOPE).isEmpty()) {
            return row.has("before") && row.get("before").isJsonPrimitive()
                    && row.has("after") && row.get("after").isJsonPrimitive()
                    && !optionalString(row, "before").isEmpty()
                    && !optionalString(row, "after").isEmpty();
        }
        for (String end : new String[] {"before", "after"}) {
            JsonObject event = row.has(end) && row.get(end).isJsonObject()
                    ? row.getAsJsonObject(end) : null;
            if (event == null || optionalString(event, "kind").isEmpty()
                    || optionalString(event, "site").isEmpty()
                    || !event.has("k") || !event.get("k").isJsonPrimitive()
                    || !event.getAsJsonPrimitive("k").isNumber()) {
                return false;
            }
        }
        return true;
    }

    static Plant read(Path file) throws IOException {
        Map<String, Map<String, Map<Integer, Root>>> markers =
                new LinkedHashMap<String, Map<String, Map<Integer, Root>>>();
        Map<String, Root> hooks = new LinkedHashMap<String, Root>();
        Map<String, Call> calls = new LinkedHashMap<String, Call>();
        Set<String> focused = new LinkedHashSet<String>();
        Map<String, Boolean> fatalArms = new LinkedHashMap<String, Boolean>();
        String anchor = null;
        for (JsonObject row : ArtifactIO.readJsonl(file)) {
            String kind = optionalString(row, KIND);
            if (!row.has(ROW) || !row.get(ROW).isJsonPrimitive()
                    || !row.getAsJsonPrimitive(ROW).isNumber()) {
                throw new IOException("a plant row without its number: "
                        + row);
            }
            int number = row.get(ROW).getAsInt();
            if (ROOT.equals(kind)) {
                focused.add(root(row, number, markers, hooks, calls));
            } else if (CLOCK_SITE.equals(kind)) {
                Call call = call(calls, row);
                call.clock = clock(row);
                call.regions.addAll(texts(row, REGIONS));
            } else if (ANSWER.equals(kind)) {
                String endpoint = optionalString(row, ENDPOINT);
                String port = optionalString(row, PORT);
                String value = optionalString(row, VALUE);
                if (endpoint.isEmpty() || port.isEmpty() || value.isEmpty()
                        || texts(row, REGIONS).isEmpty()) {
                    throw new IOException("not an answer row: " + row);
                }
                Answering answering = call(calls, row).answers
                        .computeIfAbsent(port, key -> new Answering());
                answering.regions.addAll(texts(row, REGIONS));
                answering.endpoints.put(endpoint, new Root(number, value));
            } else if (TARGET.equals(kind)) {
                String occurrence = optionalString(row, OCCURRENCE);
                if (optionalString(row, SITE).isEmpty()
                        || occurrence.isEmpty() || !row.has(VALUE)
                        || !row.get(VALUE).isJsonPrimitive()
                        || !row.getAsJsonPrimitive(VALUE).isBoolean()) {
                    throw new IOException("not a target row: " + row);
                }
                if (anchor != null && !anchor.equals(occurrence)) {
                    throw new IOException("the plant's target rows name two "
                            + "anchors, " + anchor + " and " + occurrence);
                }
                anchor = occurrence;
                fatalArms.put(optionalString(row, SITE),
                        row.get(VALUE).getAsBoolean());
            } else if (!VIEW_HOLD.equals(kind)
                    && (!ORDER.equals(kind) || !ordered(row))) {
                throw new IOException("not a plant row: " + row);
            }
        }
        if (anchor == null) {
            throw new IOException("the plant names no target: " + file);
        }
        focused.add(anchor);
        return new Plant(Collections.unmodifiableMap(markers),
                Collections.unmodifiableMap(hooks),
                Collections.unmodifiableMap(calls),
                Collections.unmodifiableSet(focused),
                Collections.unmodifiableMap(fatalArms), anchor);
    }

    private static String root(JsonObject row, int number,
                               Map<String, Map<String, Map<Integer, Root>>>
                                       markers,
                               Map<String, Root> hooks,
                               Map<String, Call> calls) throws IOException {
        String category = optionalString(row, CATEGORY);
        String rootId = optionalString(row, ROOT_ID);
        String occurrence = optionalString(row, OCCURRENCE);
        String site = optionalString(row, SITE);
        String value = optionalString(row, VALUE);
        if (rootId.isEmpty() || occurrence.isEmpty()) {
            throw new IOException("not a root row: " + row);
        }
        if (RootCategory.CLOCK.name().equals(category)) {
            String skew = optionalString(row, SKEW);
            if (!skew.matches("-?\\d+")) {
                throw new IOException("not a clock root row: " + row);
            }
            Call call = call(calls, row);
            Clock clock = clock(row);
            call.clock = clock;
            if (call.jumps.put(occurrence, new Jump(number, rootId, clock,
                    Long.parseLong(skew))) != null) {
                throw new IOException("the plant states two clock roots at "
                        + site + " in " + occurrence);
            }
            return occurrence;
        }
        if (value.isEmpty()) throw new IOException("not a root row: " + row);
        Root root = new Root(number, value);
        String javaType = optionalString(row, JAVA_TYPE);
        if (RootCategory.FAULT.name().equals(category)) {
            if (site.isEmpty() || !("true".equals(value)
                    || "false".equals(value))) {
                throw new IOException("not a fault root row: " + row);
            }
            int invocation = row.has(INVOCATION)
                    ? row.get(INVOCATION).getAsInt() : 1;
            if (invocation < 1 || markers.computeIfAbsent(site,
                    key -> new LinkedHashMap<String, Map<Integer, Root>>())
                    .computeIfAbsent(occurrence,
                            key -> new LinkedHashMap<Integer, Root>())
                    .put(invocation, root) != null) {
                throw new IOException("the plant states two fault roots, or "
                        + "none, at " + site + " in " + occurrence
                        + " invocation " + invocation + ": " + row);
            }
        } else if (RootCategory.HOOK.name().equals(category)) {
            if (hooks.put(rootId, root) != null) {
                throw new IOException("the plant states root " + rootId
                        + " twice");
            }
        } else if (RootCategory.READ.name().equals(category)) {
            if (call(calls, row).reads.put(occurrence, new Valued(root,
                    rootId, javaType)) != null) {
                throw new IOException("the plant states two reads at " + site
                        + " in " + occurrence);
            }
        } else if (RootCategory.CONFIG.name().equals(category)
                && row.has(SITES) && row.get(SITES).isJsonArray()
                && row.getAsJsonArray(SITES).size() > 0) {
            for (JsonElement getter : row.getAsJsonArray(SITES)) {
                if (!getter.isJsonObject()) {
                    throw new IOException("not a getter call: " + row);
                }
                call(calls, getter.getAsJsonObject()).configs.add(
                        new Valued(root, rootId, javaType));
            }
        } else {
            throw new IOException("not a root row: " + row);
        }
        return occurrence;
    }

    private static Call call(Map<String, Call> calls, JsonObject row)
            throws IOException {
        String site = optionalString(row, SITE);
        String callee = optionalString(row, CALLEE);
        if (site.isEmpty() || callee.isEmpty()) {
            throw new IOException("a plant row names no call: " + row);
        }
        Call call = calls.computeIfAbsent(site, key -> new Call(callee));
        if (!call.callee.equals(callee)) {
            throw new IOException("the plant names site " + site + " with "
                    + "callees " + call.callee + " and " + callee);
        }
        return call;
    }

    private static Clock clock(JsonObject row) throws IOException {
        JsonObject clock = row.has(CLOCK) && row.get(CLOCK).isJsonObject()
                ? row.getAsJsonObject(CLOCK) : null;
        try {
            return Clock.of(clock == null || !clock.has(NANOS) ? 0L
                    : clock.get(NANOS).getAsLong(), clock == null ? ""
                    : optionalString(clock, SOURCE));
        } catch (RuntimeException notAClock) {
            throw new IOException("a plant row names no clock: " + row,
                    notAClock);
        }
    }

    private static List<String> texts(JsonObject row, String member) {
        List<String> texts = new ArrayList<String>();
        if (row.has(member) && row.get(member).isJsonArray()) {
            for (JsonElement element : row.getAsJsonArray(member)) {
                if (element.isJsonPrimitive()) texts.add(element.getAsString());
            }
        }
        return texts;
    }

    static Map<String, Set<String>> interceptions(Plant plant)
            throws IOException {
        Map<String, Set<String>> intercepted =
                new LinkedHashMap<String, Set<String>>();
        for (Map.Entry<String, Call> call : plant.calls.entrySet()) {
            String[] caller = JvmSignature.parse(SiteId.methodOf(
                    call.getKey()));
            String[] callee = JvmSignature.parse(call.getValue().callee);
            if (caller == null || callee == null) {
                throw new IOException("no JVM call at site " + call.getKey()
                        + " of " + call.getValue().callee);
            }
            intercepted.computeIfAbsent(caller[0],
                    key -> new LinkedHashSet<String>())
                    .add(callee[0] + "." + callee[1] + " " + callee[2]);
        }
        return intercepted;
    }
}
