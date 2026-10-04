package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentSkipListMap;
import java.util.concurrent.atomic.AtomicInteger;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * WHERE and BY WHOM one VM-logged event happened: its bytecode site, its
 * performing activation, and its site index.  Keyed by the session-wide
 * event id, because a {@code ReadFromExpression} names its read event id but
 * not its activation.  {@link RowPublication} owns what an activation
 * observed.
 */
final class LoggedEventSites {
    private LoggedEventSites() {
    }

    /**
     * Indexes every logged event of one location's read-out record, the one
     * every activation already performs.
     */
    static void index(JsonObject record) {
        JsonObject envelope = object(record, "envelope");
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            index(element.getAsJsonObject(), "fieldVersionId", true);
        }
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            index(element.getAsJsonObject(), "readEventId", false);
        }
    }

    /** One logged event, by the id the VM numbered it with. */
    private static void index(JsonObject node, String idKey, boolean write) {
        long id = optionalLongInteger(node, idKey, -1L);
        if (id < 0L) return;
        Logged logged = new Logged(node);
        LOGGED.putIfAbsent(Long.valueOf(id), logged);
        long activation = activationOf(node, id);
        OccurrenceAddress performer = RowRuntime.occurrenceAt(activation);
        // Every record that states the site files the event, not only the
        // first to name its id: that one may be a record with no site.
        if (performer == null || !logged.states()) return;
        AT_SITE.computeIfAbsent(group(performer, logged.site(write)),
                key -> new Group()).add(id, activation);
    }

    /**
     * An endpoint without its k: the occurrence that performed the event and
     * its site.  Never the activation: a loop's stores after a folded callee
     * region returns are stated under that callee's activation, one per turn.
     */
    private static String group(OccurrenceAddress performer, String site) {
        return performer.id() + "|" + site;
    }

    /**
     * Where one logged event ran, and under which activation.  Only these
     * fields: keeping the record would retain its whole value expression.
     */
    private static final class Logged {
        private final long activation;
        private final String className;
        private final String method;
        private final String descriptor;
        private final int bci;

        private Logged(JsonObject node) {
            this.activation = optionalLongInteger(node,
                    "regionEnterEventId", -1L);
            JsonObject site = object(node, "site");
            this.className = site == null ? ""
                    : optionalString(site, "className");
            this.method = site == null ? ""
                    : optionalString(site, "methodName");
            this.descriptor = site == null ? ""
                    : optionalString(site, "methodDescriptor");
            this.bci = site == null ? -1
                    : optionalInteger(site, "bci", -1);
        }

        private boolean states() {
            return !className.isEmpty() && !method.isEmpty();
        }

        /** The method half of {@link #site}, a scope map row's
         *  {@code vmSite}: {@code <class>#<method><descriptor>}. */
        private String method() {
            String site = site(false);
            return site.substring(0, site.lastIndexOf('#'));
        }

        /**
         * The one spelling of the site, and the one place a VM class name is
         * converted to source form.  Stabilised BEFORE slashes become dots:
         * in {@code <Outer>$$Lambda$14/123} the slash separates the hash.
         */
        private String site(boolean write) {
            return Endpoint.stateSite(
                    JvmNames.stable(className).replace('/', '.'), method,
                    descriptor, Math.max(0, bci), write);
        }
    }

    /** Every logged event of this session, by version or read event id. */
    private static final Map<Long, Logged> LOGGED =
            new ConcurrentHashMap<Long, Logged>();

    /** One occurrence's logged events at one site. */
    private static final Map<String, Group> AT_SITE =
            new ConcurrentHashMap<String, Group>();

    /**
     * One {@link #AT_SITE} group: event id -&gt; activation, and how many
     * (a skip list counts itself by walking, once per row it ranked).
     */
    private static final class Group {
        private final NavigableMap<Long, Long> events =
                new ConcurrentSkipListMap<Long, Long>();
        private final AtomicInteger size = new AtomicInteger();

        private void add(long id, long activation) {
            if (events.putIfAbsent(id, activation) == null) {
                size.incrementAndGet();
            }
        }
    }

    /**
     * One {@link #AT_SITE} group ranked: each event's frames
     * ({@link FrameJournal}; null is an event this run cannot place) and k.
     * An event's k counts only the events before it, so a group that grew
     * after its last ranked event is ranked on from there.
     */
    private static final class Ranked {
        private int size;
        private long last = Long.MIN_VALUE;
        private final Map<String, Integer> made = new HashMap<String, Integer>();
        private final Map<Long, ExecutionIndex> frames =
                new HashMap<Long, ExecutionIndex>();
        private final Map<Long, Integer> ranks = new HashMap<Long, Integer>();

        /** Ranks the group's events after the last one ranked. */
        private void extend(Group group) {
            for (Map.Entry<Long, Long> logged
                    : group.events.tailMap(last, false).entrySet()) {
                Long event = logged.getKey();
                ExecutionIndex stood = FrameJournal.framesAt(
                        logged.getValue(), event);
                String key = stood == null ? "" : stood.render();
                Integer k = made.get(key);
                made.put(key, k == null ? 1 : k + 1);
                frames.put(event, stood);
                ranks.put(event, k == null ? 0 : k);
                last = event;
                size++;
            }
        }
    }

    /** Each group ranked once, again only after it grew. */
    private static final Map<String, Ranked> RANKED =
            new ConcurrentHashMap<String, Ranked>();

    /**
     * A logged event's site ({@link Logged#site}); the descriptor separates
     * overloads.  An event with no stated site is a gap spelled by its
     * location.
     */
    static String site(JsonObject node, String locationKey,
                                     long eventId, boolean write) {
        Logged own = node == null ? null : new Logged(node);
        Logged record = eventId < 0L ? null
                : LOGGED.get(Long.valueOf(eventId));
        Logged site = own != null && own.states() ? own
                : record != null && record.states() ? record : null;
        if (site == null) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    locationKey + "#" + eventId,
                    "the VM states no bytecode site for this "
                            + (write ? "version" : "read")
                            + ", so the endpoint's site is its location and"
                            + " distinguishes no event of it");
            return Endpoint.stateSite(locationKey, "UNSTATED_SITE", 0, write);
        }
        return site.site(write);
    }

    /** The method a logged event states it ran in, as a scope map row's
     *  {@code vmSite} spells it; "" when it states no site. */
    static String method(JsonObject node) {
        Logged own = node == null ? null : new Logged(node);
        return own != null && own.states() ? own.method() : "";
    }

    /**
     * The occurrence that performed one logged event, or null with a gap.
     * The VM-stated activation, never whichever occurrence published the
     * location's log.
     */
    static OccurrenceAddress performer(JsonObject node,
                                               String locationKey,
                                               long eventId, boolean write) {
        long activation = activationOf(node, eventId);
        OccurrenceAddress performer = RowRuntime.occurrenceAt(activation);
        if (performer != null) return performer;
        RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                locationKey + "#" + eventId,
                "this " + (write ? "version" : "read") + " states activation "
                        + activation + ", which is no activation of this"
                        + " session, so the run cannot say which occurrence"
                        + " performed it and states no row for it");
        return null;
    }

    /** The activation the event states, its own or its log record's. */
    private static long activationOf(JsonObject node, long eventId) {
        long activation = optionalLongInteger(node, "regionEnterEventId", -1L);
        if (activation > 0L) return activation;
        Logged record = eventId < 0L ? null
                : LOGGED.get(Long.valueOf(eventId));
        return record == null ? -1L : record.activation;
    }

    /**
     * The site index of one logged event: the frames it stood on, then the
     * event itself as {@code (site, k)}, k its rank by event id among its
     * occurrence's logged events at {@code site} on the same frames -- DEI's
     * count per (site, stack).  Counted over every logged event, published
     * or not, so a flip that changes which reads are symbolic moves no k;
     * without it one loop's reads at one bytecode share one endpoint id.
     * Frames the journal cannot place are {@code ""}, with a gap.
     * Synchronized: a {@link Ranked} grows in place.
     */
    static synchronized String siteIndex(JsonObject node, String locationKey,
                                         long eventId, String site,
                                         boolean write) {
        long activation = activationOf(node, eventId);
        OccurrenceAddress performer = RowRuntime.occurrenceAt(activation);
        String group = performer == null ? "" : group(performer, site);
        Group atSite = AT_SITE.get(group);
        Ranked ranked = null;
        if (atSite != null && atSite.events.containsKey(eventId)) {
            ranked = RANKED.get(group);
            int size = atSite.size.get();
            if (ranked != null && ranked.size != size) {
                ranked.extend(atSite);
                // One arrived before the last ranked: every later k moves.
                if (ranked.size != size) ranked = null;
            }
            if (ranked == null) {
                ranked = new Ranked();
                ranked.extend(atSite);
                RANKED.put(group, ranked);
            }
        }
        ExecutionIndex frames = ranked != null ? ranked.frames.get(eventId)
                : FrameJournal.framesAt(activation, eventId);
        if (frames == null) {
            RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                    locationKey + "#" + eventId,
                    "this " + (write ? "version" : "read")
                            + (activation <= 0L
                            ? " states no region activation, so no frame"
                            + " journal can place it"
                            : " ran under activation " + activation
                            + " with no frame journal entry below its event"
                            + " id")
                            + "; the endpoint carries no frames");
            frames = ExecutionIndex.empty();
        }
        // An event the VM log never named counts none before it.
        int k = ranked == null ? 0 : ranked.ranks.get(eventId);
        List<Frame> index = new ArrayList<Frame>(frames.frames());
        // A frame's site carries no '/': the descriptor's, in source form.
        index.add(Frame.of(site.replace('/', '.'), k));
        return ExecutionIndex.of(index).render();
    }
}
