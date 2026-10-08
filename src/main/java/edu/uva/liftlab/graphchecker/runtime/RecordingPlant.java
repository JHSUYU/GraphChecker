package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
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

/**
 * A native reproduction's plant (PIPELINE §10b): the world a confirmed
 * witness ran in, planted in the recording weave on a stock JDK, so a
 * finding is run again without the concolic VM ({@code run_engine.sh}
 * REPRODUCE), and the one question such a run answers: does the planted
 * world take the throw's fatal arm at the claim's anchor.
 *
 * <p>{@code -Dcausynth.plant=<file>} names the plant, JSONL written by
 * CONFIRM's own code ({@code explore.ConfirmMain --plant}), each row
 * numbered ({@value #ROW}); a row the run applied is an {@link #APPLIED}
 * trace row naming its number.  A row plants inside the recording window
 * only, under an occurrence named by its id ({@link OccurrenceAddress#id}),
 * as a focused replay matches its occurrences; the occurrences enclosing a
 * call are the recording weave's region entries on its thread
 * ({@code CausynthTraceRecorder#enclosingOccurrences}).</p>
 * <ul>
 *   <li>{@code ROOT FAULT {rootId, occurrence, siteId, value}}: a marker call
 *   ({@code Debug.makeSymbolicBoolean}) answers the value at that call site
 *   under the occurrence; otherwise, and always without a plant, its
 *   recorded polarity {@code false}.  A {@code true} answer is a door fault
 *   for the thread's identity as in a replay ({@link Identity#doorFaulted}).</li>
 *   <li>{@code ROOT HOOK {rootId, occurrence, value}}: a tree's symbolize
 *   hook of that root writes the value into the field it names
 *   ({@link RootMint#writeModeledField}) under an occurrence the
 *   confirmation focuses -- the anchor, or the mint occurrence of any root
 *   of the plant ({@link Plant#focused}) -- as a replay's mint plants it.</li>
 *   <li>Values at a call's return, which {@link PlantAgent} hands here
 *   ({@link #returned(long)} and its overloads) after every call of a
 *   callee the plant names in a class it names; the call is the one the
 *   recording weave's own call-site context states, by {@code siteId} and
 *   callee ({@code CausynthTraceRecorder#currentCallSiteContext}):
 *   <ul>
 *     <li>{@code ROOT CONFIG {rootId, occurrence, sites: [{siteId, callee}],
 *     javaType, value}}: every return of those getter calls is the value --
 *     a configuration is the world's, whatever occurrence reads it, as in a
 *     replay;</li>
 *     <li>{@code ROOT READ {rootId, occurrence, siteId, callee, javaType,
 *     value}}: the accessor call's return under the occurrence;</li>
 *     <li>{@code ROOT CLOCK {rootId, occurrence, siteId, callee, clock:
 *     {nanos, source}, skew}}: the first return of the clock call under the
 *     occurrence is the host's reading plus the skew, and a jump of that
 *     occurrence's node's clock ({@link NodeClocks}): every later declared
 *     reading of that clock on that node runs on from it;</li>
 *     <li>{@code CLOCK_SITE {siteId, callee, clock, regions}}: a declared
 *     clock reading, which reads the host's clock plus the skew of the
 *     jump before it on its node's clock, its node the one of its innermost
 *     enclosing occurrence of a region in {@code regions}.  "Before" is
 *     this run's real order ({@link #PLACES}): a native run has no recorded
 *     place.  A context row, applied by nobody;</li>
 *     <li>{@code ANSWER {endpoint, port, siteId, callee, regions, value}}:
 *     the value a port's call-return capture returns, carried and named as
 *     a replay's attach names it inside its innermost enclosing occurrence
 *     of a region in {@code regions} ({@link HandoffMint#answerNatively}),
 *     the answer written at the endpoint's leaf.</li>
 *   </ul></li>
 *   <li>{@code ORDER {before, after}}: CONFIRM's own row, held as a CONFIRM
 *   run holds it ({@link Confirmation}, which reads this file in a planted
 *   run).  Held, the row is applied; an activation that waits is a
 *   {@link #HOLDING} row, and one whose wait times out an {@link #UNHELD}
 *   row: what the run states, never a refutation.</li>
 *   <li>{@code TARGET {occurrence: <the anchor's id>, siteId: <a TARGET_SITE
 *   guard>, value: <its fatal arm>}} per guard of the target.  A decision
 *   there that takes the fatal arm inside the window is a {@link #FATAL}
 *   trace row, saying whether an enclosing occurrence is the anchor; at the
 *   anchor the run ends ({@link JUnitMethodRunner#exit}), its question
 *   answered, as a focused replay ends at its witness.</li>
 * </ul>
 * A value that cannot be read as what the call returns is an
 * {@link #UNWRITTEN} row, as a HOOK's write that fails.
 */
public final class RecordingPlant {
    static final String PROPERTY = "causynth.plant";
    /** The trace event of one plant row applied: a root planted, an order
     *  held, an answer written. */
    static final String APPLIED = "PLANT_APPLIED";
    /** An ORDER's activation waits for what the model orders before it. */
    static final String HOLDING = "PLANT_HOLDING";
    /** An ORDER the run did not hold within the order's timeout. */
    static final String UNHELD = "PLANT_UNHELD";
    /** A row reached whose value could not be planted. */
    static final String UNWRITTEN = "PLANT_UNWRITTEN";
    /** The trace event of one decision of the planted world's fatal arm. */
    static final String FATAL = "PLANT_FATAL";
    /** A root the world assigns, planted where it is minted. */
    public static final String ROOT = "ROOT";
    /** CONFIRM's ORDER row ({@link Confirmation}). */
    public static final String ORDER = "ORDER";
    /** A guard of the target and its fatal arm. */
    public static final String TARGET = "TARGET";
    /** A declared clock reading: runs on its node's clock. */
    public static final String CLOCK_SITE = "CLOCK_SITE";
    /** An attach the world answers. */
    public static final String ANSWER = "ANSWER";
    public static final String KIND = "kind";
    public static final String ROW = "row";
    public static final String CATEGORY = "category";
    public static final String ROOT_ID = "rootId";
    public static final String OCCURRENCE = "occurrence";
    public static final String SITE = "siteId";
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

    /** Read once: the JVM's own property. */
    private static final boolean PLANTING = !file().isEmpty();
    private static volatile Plant plant;
    private static final AtomicBoolean ENDED = new AtomicBoolean();
    /** The run's own order of declared clock readings: a reading's place
     *  on its node's clock ({@link NodeClocks}). */
    private static final AtomicLong PLACES = new AtomicLong();
    /** "occurrence id|root id" of every clock root planted: an
     *  occurrence's root is its first reading of the call. */
    private static final Set<String> CLOCKED = ConcurrentHashMap.newKeySet();
    /** The rows stated applied or unwritten: each once. */
    private static final Set<Integer> STATED = ConcurrentHashMap.newKeySet();

    private RecordingPlant() {
    }

    static void resetForTests() {
        PLACES.set(0L);
        CLOCKED.clear();
        STATED.clear();
        NodeClocks.reset();
    }

    /** Whether this run plants a world: a native reproduction, where the
     *  workload's checks of the recording's world do not hold
     *  ({@link CausynthTraceRecorder#replaying}). */
    static boolean planting() {
        return PLANTING;
    }

    /** The plant file this run was handed, or "". */
    static String file() {
        return System.getProperty(PROPERTY, "").trim();
    }

    /** One root or answer of the plant: its row and the value planted. */
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

    /** A root whose value a call returns: CONFIG and READ. */
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

    /** A clock root: the jump its mint makes. */
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

    /** One port's answers at a call: the regions declaring the capture IN,
     *  each answered endpoint. */
    static final class Answering {
        final Set<String> regions = new LinkedHashSet<String>();
        final Map<String, Root> endpoints = new LinkedHashMap<String, Root>();
    }

    /** One call whose return the plant reads ({@link PlantAgent}). */
    static final class Call {
        final String callee;
        /** A declared clock reading's clock, or null. */
        Clock clock;
        /** The regions declaring the clock reading. */
        final Set<String> regions = new LinkedHashSet<String>();
        /** Clock roots, by mint occurrence id. */
        final Map<String, Jump> jumps = new LinkedHashMap<String, Jump>();
        final List<Valued> configs = new ArrayList<Valued>();
        /** READ roots, by mint occurrence id. */
        final Map<String, Valued> reads = new LinkedHashMap<String, Valued>();
        /** Answers, by port. */
        final Map<String, Answering> answers =
                new LinkedHashMap<String, Answering>();

        Call(String callee) {
            this.callee = callee;
        }
    }

    /** One plant file. */
    static final class Plant {
        /** FAULT markers: call site, then occurrence id, then the root. */
        final Map<String, Map<String, Root>> markers;
        /** HOOK roots, by root id. */
        final Map<String, Root> hooks;
        /** The calls whose returns it reads, by site id. */
        final Map<String, Call> calls;
        /** The occurrences the confirmation focuses, by id: the anchor and
         *  every root's mint occurrence ({@code FocusedReplay#focused}). */
        final Set<String> focused;
        /** Guard site -> its fatal arm. */
        final Map<String, Boolean> fatalArms;
        /** The claim's anchor, by occurrence id. */
        final String anchor;

        Plant(Map<String, Map<String, Root>> markers,
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

    /** The marker {@code name}'s answer at the call running now. */
    static boolean marker(String name) {
        if (!PLANTING || !RecordingWindow.opened()) return false;
        CausynthTraceRecorder.ActiveCallSiteContext site =
                CausynthTraceRecorder.currentCallSiteContext();
        if (site == null) return false;
        Map<String, Root> rows = plant().markers.get(site.siteId());
        String occurrence = plantedOccurrence(rows,
                CausynthTraceRecorder.enclosingOccurrences());
        if (occurrence == null) return false;
        Root root = rows.get(OccurrenceAddress.parse(occurrence).id());
        boolean value = Boolean.parseBoolean(root.value);
        CausynthTraceRecorder.plantRoot(APPLIED, root.row, name, occurrence,
                String.valueOf(value));
        if (value) Identity.doorFaulted(name);
        return value;
    }

    /** A tree's symbolize hook of {@code rootId} on {@code owner}'s field:
     *  the planted value written there under a focused occurrence. */
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

    /** What a plant-named call returned, as the planted world has it
     *  ({@link PlantAgent} calls it after every such call). */
    public static long returned(long value) {
        if (!PLANTING) return value;
        Object planted = intercept(value);
        return planted instanceof Number ? ((Number) planted).longValue()
                : value;
    }

    /** {@link #returned(long)} for an int, short, byte or char return. */
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

    /** {@link #returned(long)} for a reference return; the agent casts it
     *  back to the call's type. */
    public static Object returned(Object value) {
        return PLANTING ? intercept(value) : value;
    }

    /** The call running now, as the recording weave states it, inside the
     *  window. */
    private static Object intercept(Object host) {
        if (!RecordingWindow.opened()) return host;
        CausynthTraceRecorder.ActiveCallSiteContext site =
                CausynthTraceRecorder.currentCallSiteContext();
        return site == null ? host : returnedAt(plant(), site.siteId(),
                site.declaredCallee(),
                CausynthTraceRecorder.enclosingOccurrences(), host);
    }

    /** What call {@code siteId} of {@code callee} returns under {@code
     *  enclosing} (innermost first), if the plant reads it, applied in
     *  order: a configuration, an accessor's read, a clock, answers. */
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

    /** A CONFIG or READ root's value, read as what the call returns. */
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

    /**
     * A clock call's return on its node's clock: the first under a clock
     * root's mint occurrence plants the root (the host's reading plus its
     * skew) and jumps the node's clock; every other declared reading reads
     * the host plus the skew of the latest jump at or before it.
     */
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
                // A clock stating no source is on no node's order: the
                // plant moves this reading alone.
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

    /** The answers one port's capture takes at the call running now. */
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

    /** What a call of {@code host}'s runtime type returns: its box's
     *  primitive, else the stated type, else its own class. */
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

    /** What one ORDER row of the plant came to ({@link Confirmation}):
     *  {@code event} one of {@link #APPLIED}, {@link #HOLDING},
     *  {@link #UNHELD}. */
    static void ordered(String event, int row, String after,
                        String waitingFor) {
        CausynthTraceRecorder.plantOrdered(event, row, after, waitingFor);
    }

    /** A decision the recording observed ({@code outcome} null when it took
     *  no arm a guard names): at a target guard's fatal arm, stated, and at
     *  the anchor the run's end. */
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

    /** Of the occurrences enclosing a decision, the anchor's, or null. */
    static String anchorOf(List<String> enclosing, String anchor) {
        for (String occurrence : enclosing) {
            if (OccurrenceAddress.parse(occurrence).id().equals(anchor)) {
                return occurrence;
            }
        }
        return null;
    }

    /** Of the occurrences enclosing a call, innermost first, the first
     *  the confirmation focuses (by id), or null. */
    static String focusedOccurrence(Set<String> focused,
                                    List<String> enclosing) {
        for (String occurrence : enclosing) {
            if (focused.contains(OccurrenceAddress.parse(occurrence).id())) {
                return occurrence;
            }
        }
        return null;
    }

    /** Of the occurrences enclosing a call, innermost first, the first
     *  {@code byOccurrence} plants at (by id), or null. */
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

    /** Of the occurrences enclosing a call, innermost first, the first of
     *  a region in {@code regions}, or null. */
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

    /** The run's one end, on a thread of its own: the decision's thread is
     *  the workload's, and the end waits for what is live to settle. */
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
                    // A run told to plant that cannot is no reproduction.
                    throw new IllegalStateException("the plant -D" + PROPERTY
                            + "=" + file() + " is unreadable: "
                            + unreadable.getMessage(), unreadable);
                }
            }
            return plant;
        }
    }

    /**
     * A plant file's rows.  A row of another kind, without its number, a
     * ROOT of no plantable category or missing what its category needs (a
     * FAULT its call site and a boolean, a CONFIG its getter calls, a READ
     * or CLOCK its call, a CLOCK its clock and an integral skew), a call
     * site named with two callees, a TARGET naming no guard or a boolean
     * arm, and an ORDER naming no activation are refused; so is a plant
     * whose target rows name no anchor or two, since the run would answer
     * nothing.  ORDER rows are {@link Confirmation}'s.
     */
    static Plant read(Path file) throws IOException {
        Map<String, Map<String, Root>> markers =
                new LinkedHashMap<String, Map<String, Root>>();
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
            } else if (!ORDER.equals(kind)
                    || optionalString(row, "before").isEmpty()
                    || optionalString(row, "after").isEmpty()) {
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

    /** One ROOT row into what plants it; returns the occurrence it is
     *  minted at.  A root stated twice is refused. */
    private static String root(JsonObject row, int number,
                               Map<String, Map<String, Root>> markers,
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
            markers.computeIfAbsent(site,
                    key -> new LinkedHashMap<String, Root>())
                    .put(occurrence, root);
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

    /** The call a row names by site and callee; one site, one callee. */
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

    /**
     * The calls a plant has a run intercept ({@link PlantAgent}): each
     * caller class (internal name) to the callees it calls whose returns the
     * plant reads, as {@code owner.name descriptor}.  A site or callee no
     * JVM signature parses from is refused.
     */
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
