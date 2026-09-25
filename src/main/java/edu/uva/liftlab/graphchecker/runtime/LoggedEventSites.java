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
        OccurrenceAddress performer = RowRuntime.occurrenceAt(
                activationOf(node, id));
        // Every record that states the site files the event, not only the
        // first to name its id: that one may be a record with no site.
        if (performer == null || !logged.states()) return;
        AT_SITE.computeIfAbsent(group(performer, logged.site(write)),
                key -> new ConcurrentSkipListMap<Long, Long>())
                .putIfAbsent(id, activationOf(node, id));
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

    /** One occurrence's logged events at one site: event id -> activation. */
    private static final Map<String, NavigableMap<Long, Long>> AT_SITE =
            new ConcurrentHashMap<String, NavigableMap<Long, Long>>();

    /** One {@link #AT_SITE} group ranked: each event's frames and k. */
    private static final class Ranked {
        private final int size;
        private final Map<Long, String> frames = new HashMap<Long, String>();
        private final Map<Long, Integer> ranks = new HashMap<Long, Integer>();

        private Ranked(NavigableMap<Long, Long> group) {
            Map<String, Integer> made = new HashMap<String, Integer>();
            int counted = 0;
            for (Map.Entry<Long, Long> logged : group.entrySet()) {
                Long event = logged.getKey();
                String stood = framesOf(logged.getValue(), event);
                String key = stood == null ? "" : stood;
                Integer k = made.get(key);
                made.put(key, k == null ? 1 : k + 1);
                frames.put(event, stood);
                ranks.put(event, k == null ? 0 : k);
                counted++;
            }
            this.size = counted;
        }
    }

    /**
     * The rendered frames one logged event stood on ({@link FrameJournal}):
     * null is an event this run cannot place (a gap), {@code ""} one placed
     * at the region entry on no frames.
     */
    private static String framesOf(long activation, long eventId) {
        ExecutionIndex index = FrameJournal.framesAt(activation, eventId);
        return index == null ? null : index.render();
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
     */
    static String siteIndex(JsonObject node, String locationKey,
                            long eventId, String site, boolean write) {
        long activation = activationOf(node, eventId);
        OccurrenceAddress performer = RowRuntime.occurrenceAt(activation);
        String group = performer == null ? "" : group(performer, site);
        NavigableMap<Long, Long> atSite = AT_SITE.get(group);
        Ranked ranked = null;
        if (atSite != null && atSite.containsKey(eventId)) {
            ranked = RANKED.get(group);
            if (ranked == null || ranked.size != atSite.size()) {
                ranked = new Ranked(atSite);
                RANKED.put(group, ranked);
            }
        }
        String frames = ranked != null ? ranked.frames.get(eventId)
                : framesOf(activation, eventId);
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
            frames = "";
        }
        // An event the VM log never named counts none before it.
        int k = ranked == null ? 0 : ranked.ranks.get(eventId);
        List<Frame> index =
                new ArrayList<Frame>(ExecutionIndex.parse(frames).frames());
        // A frame's site carries no '/': the descriptor's, in source form.
        index.add(Frame.of(site.replace('/', '.'), k));
        return ExecutionIndex.of(index).render();
    }
}
