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

final class LoggedEventSites {
    private LoggedEventSites() {
    }

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

    private static void index(JsonObject node, String idKey, boolean write) {
        long id = optionalLongInteger(node, idKey, -1L);
        if (id < 0L) return;
        Logged logged = new Logged(node);
        LOGGED.putIfAbsent(Long.valueOf(id), logged);
        long activation = activationOf(node, id);
        OccurrenceAddress performer = RowRuntime.occurrenceAt(activation);
        if (performer == null || !logged.states()) return;
        AT_SITE.computeIfAbsent(group(performer, logged.site(write)),
                key -> new Group()).add(id, activation);
    }

    private static String group(OccurrenceAddress performer, String site) {
        return performer.id() + "|" + site;
    }

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

        private String method() {
            String site = site(false);
            return site.substring(0, site.lastIndexOf('#'));
        }

        private String site(boolean write) {
            return Endpoint.stateSite(
                    JvmNames.stable(className).replace('/', '.'), method,
                    descriptor, Math.max(0, bci), write);
        }
    }

    private static final Map<Long, Logged> LOGGED =
            new ConcurrentHashMap<Long, Logged>();

    private static final Map<String, Group> AT_SITE =
            new ConcurrentHashMap<String, Group>();

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

    private static final class Ranked {
        private int size;
        private long last = Long.MIN_VALUE;
        private final Map<String, Integer> made = new HashMap<String, Integer>();
        private final Map<Long, ExecutionIndex> frames =
                new HashMap<Long, ExecutionIndex>();
        private final Map<Long, Integer> ranks = new HashMap<Long, Integer>();

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

    private static final Map<String, Ranked> RANKED =
            new ConcurrentHashMap<String, Ranked>();

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

    static String statedSite(JsonObject node) {
        Logged own = node == null ? null : new Logged(node);
        return own != null && own.states() ? own.site(true) : "";
    }

    static String method(JsonObject node) {
        Logged own = node == null ? null : new Logged(node);
        return own != null && own.states() ? own.method() : "";
    }

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

    private static long activationOf(JsonObject node, long eventId) {
        long activation = optionalLongInteger(node, "regionEnterEventId", -1L);
        if (activation > 0L) return activation;
        Logged record = eventId < 0L ? null
                : LOGGED.get(Long.valueOf(eventId));
        return record == null ? -1L : record.activation;
    }

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
        int k = ranked == null ? 0 : ranked.ranks.get(eventId);
        List<Frame> index = new ArrayList<Frame>(frames.frames());
        index.add(Frame.of(site.replace('/', '.'), k));
        return ExecutionIndex.of(index).render();
    }
}
