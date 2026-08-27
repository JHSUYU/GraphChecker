package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The one order domain, read back from the session's event ledger: every
 * causal channel the VM recorded lives in one partial relation over one
 * event-id space, so events on different channels are comparable. It answers
 * precedence, the relation restricted to a set, and whether a candidate edge
 * can be admitted - never a schedule. Acyclicity is recomputed over the
 * delivered edges; a cycle yields the empty domain with a named {@link
 * #fault()}.
 */
public final class SessionOrderDomain {

    /** The VM's own order-proposal statuses (eventLedger.hpp). */
    public static final int ORDER_OK = 0;
    public static final int ORDER_NOT_OPEN = -1;
    public static final int ORDER_UNKNOWN_EVENT = -2;
    public static final int ORDER_SELF_EDGE = -3;
    public static final int ORDER_CYCLIC = -4;

    /** Edge kind stamped on a pair related only through other events. */
    public static final String TRANSITIVE = "TRANSITIVE";

    private final boolean open;
    private final String fault;
    private final Map<Long, JsonObject> events;
    private final Map<Long, Set<Long>> successors;
    private final Map<String, String> directKinds;

    private SessionOrderDomain(boolean open, String fault,
                               Map<Long, JsonObject> events,
                               Map<Long, Set<Long>> successors,
                               Map<String, String> directKinds) {
        this.open = open;
        this.fault = fault;
        this.events = events;
        this.successors = successors;
        this.directKinds = directKinds;
    }

    /** An empty domain: no events, no order, and it knows it. */
    public static SessionOrderDomain empty() { return empty(""); }

    private static SessionOrderDomain empty(String fault) {
        return new SessionOrderDomain(false, fault,
                Collections.<Long, JsonObject>emptyMap(),
                new LinkedHashMap<Long, Set<Long>>(),
                new LinkedHashMap<String, String>());
    }

    /**
     * Reads one admitted ledger record, or the envelope inside it. A record
     * that fails {@link SharedStateEvidence} admission, or whose delivered
     * edges close a cycle on any channel, yields the empty domain.
     */
    public static SessionOrderDomain of(JsonObject ledgerRecordOrEnvelope) {
        JsonObject envelope = ledgerRecordOrEnvelope;
        if (envelope != null
                && SharedStateEvidence.LEDGER_RECORD_KIND.equals(
                string(envelope, "kind"))) {
            envelope = object(envelope, "envelope");
        }
        if (envelope == null) return empty("no ledger envelope");
        String admission = SharedStateEvidence.ledgerFault(envelope);
        if (!admission.isEmpty()) return empty(admission);
        Map<Long, JsonObject> events = new LinkedHashMap<>();
        for (JsonElement element : array(envelope, "events")) {
            JsonObject event = element.getAsJsonObject();
            events.put(longInteger(event, "eventId", 0L), event.deepCopy());
        }
        Map<Long, Set<Long>> successors = new LinkedHashMap<>();
        Map<String, String> directKinds = new LinkedHashMap<>();
        for (JsonElement element : array(envelope, "order")) {
            JsonObject edge = element.getAsJsonObject();
            long before = longInteger(edge, "beforeEventId", 0L);
            long after = longInteger(edge, "afterEventId", 0L);
            successorsOf(successors, before).add(after);
            // One pair may carry several kinds; the first recorded one names
            // it, so a program-order pair is not renamed by a later
            // synchronization edge between the same two events.
            String key = before + ">" + after;
            if (!directKinds.containsKey(key)) {
                directKinds.put(key, string(edge, "edgeKind"));
            }
        }
        String cycle = cycleFault(events.keySet(), successors);
        if (!cycle.isEmpty()) return empty(cycle);
        return new SessionOrderDomain(true, "", events, successors,
                directKinds);
    }

    /** Names one cycle of the whole delivered relation, or "" when it has none. */
    private static String cycleFault(Set<Long> events,
                                     Map<Long, Set<Long>> successors) {
        Set<Long> settled = new LinkedHashSet<>();
        for (Long root : events) {
            if (settled.contains(root)) continue;
            Set<Long> onStack = new LinkedHashSet<>();
            List<Long> path = new ArrayList<>();
            Deque<Object[]> frontier = new ArrayDeque<>();
            frontier.push(new Object[]{root, null});
            while (!frontier.isEmpty()) {
                Object[] frame = frontier.peek();
                Long current = (Long) frame[0];
                if (frame[1] == null) {
                    if (settled.contains(current)) {
                        frontier.pop();
                        continue;
                    }
                    if (!onStack.add(current)) {
                        return "order domain closes a cycle at event "
                                + current + " through "
                                + render(path, current);
                    }
                    path.add(current);
                    Set<Long> next = successors.get(current);
                    frame[1] = next == null
                            ? new ArrayDeque<Long>()
                            : new ArrayDeque<>(next);
                }
                @SuppressWarnings("unchecked")
                Deque<Long> pending = (Deque<Long>) frame[1];
                if (pending.isEmpty()) {
                    frontier.pop();
                    onStack.remove(current);
                    path.remove(path.size() - 1);
                    settled.add(current);
                    continue;
                }
                Long successor = pending.poll();
                if (onStack.contains(successor)) {
                    return "order domain closes a cycle at event " + successor
                            + " through " + render(path, successor);
                }
                if (!settled.contains(successor)) {
                    frontier.push(new Object[]{successor, null});
                }
            }
        }
        return "";
    }

    private static String render(List<Long> path, Long closing) {
        StringBuilder rendered = new StringBuilder();
        boolean started = false;
        for (Long event : path) {
            if (!started && !event.equals(closing)) continue;
            started = true;
            rendered.append(event).append(" -> ");
        }
        if (!started) {
            for (Long event : path) rendered.append(event).append(" -> ");
        }
        return rendered.append(closing).toString();
    }

    /** Why this domain holds no relation ("" when it holds one, so a refusal
     * and an empty session stay distinguishable). */
    public String fault() { return fault; }

    private static Set<Long> successorsOf(Map<Long, Set<Long>> successors,
                                          long event) {
        Set<Long> next = successors.get(event);
        if (next == null) {
            next = new LinkedHashSet<>();
            successors.put(event, next);
        }
        return next;
    }

    /** Whether this domain came from an open session's ledger. */
    public boolean open() { return open; }

    public boolean isEmpty() { return events.isEmpty(); }

    public boolean knows(long eventId) { return events.containsKey(eventId); }

    /** The region occurrence one event belongs to, or "". */
    public String regionOf(long eventId) {
        return string(events.get(eventId), "regionId");
    }

    /** Every recorded event, ascending. */
    public Set<Long> eventIds() {
        return Collections.unmodifiableSet(new TreeSet<>(events.keySet()));
    }

    /**
     * Whether {@code before} provably precedes {@code after}, directly or
     * transitively. False means the run showed no order, not the reverse.
     */
    public boolean orderedBefore(long before, long after) {
        if (before == after || !knows(before) || !knows(after)) return false;
        Set<Long> seen = new LinkedHashSet<>();
        Deque<Long> frontier = new ArrayDeque<>();
        frontier.push(before);
        while (!frontier.isEmpty()) {
            long current = frontier.pop();
            Set<Long> next = successors.get(current);
            if (next == null) continue;
            for (Long successor : next) {
                if (successor == after) return true;
                if (seen.add(successor)) frontier.push(successor);
            }
        }
        return false;
    }

    /** Every directly recorded edge, in insertion order, once per pair. */
    public List<JsonObject> directEdges() {
        List<JsonObject> edges = new ArrayList<>();
        for (Map.Entry<String, String> entry : directKinds.entrySet()) {
            int separator = entry.getKey().indexOf('>');
            JsonObject edge = new JsonObject();
            edge.addProperty("beforeEventId", Long.parseLong(
                    entry.getKey().substring(0, separator)));
            edge.addProperty("afterEventId", Long.parseLong(
                    entry.getKey().substring(separator + 1)));
            edge.addProperty("edgeKind", entry.getValue());
            edges.add(edge);
        }
        return edges;
    }

    /**
     * Offers one candidate edge with the ledger's own semantics: self edges,
     * unknown events and cyclic proposals are refused and add nothing; an
     * admitted candidate joins the relation later proposals are checked on.
     */
    public int propose(long before, long after) {
        if (!open) return ORDER_NOT_OPEN;
        if (before == after) return ORDER_SELF_EDGE;
        if (!knows(before) || !knows(after)) return ORDER_UNKNOWN_EVENT;
        if (orderedBefore(after, before)) return ORDER_CYCLIC;
        if (!orderedBefore(before, after)) {
            successorsOf(successors, before).add(after);
        }
        return ORDER_OK;
    }

    /** Names one proposal status, so a refusal is reported and not guessed. */
    public static String statusName(int status) {
        switch (status) {
            case ORDER_OK:
                return "OK";
            case ORDER_NOT_OPEN:
                return "NOT_OPEN";
            case ORDER_UNKNOWN_EVENT:
                return "UNKNOWN_EVENT";
            case ORDER_SELF_EDGE:
                return "SELF_EDGE";
            case ORDER_CYCLIC:
                return "CYCLIC";
            default:
                return "UNKNOWN";
        }
    }

    /**
     * The relation restricted to {@code selected}, by reachability rather
     * than by direct edges: a pair ordered only through events the slice
     * drops would otherwise be reported as concurrent.
     */
    public List<JsonObject> project(Collection<Long> selected) {
        Set<Long> known = new TreeSet<>();
        for (Long event : selected) {
            if (event != null && knows(event)) known.add(event);
        }
        List<JsonObject> relation = new ArrayList<>();
        for (Long before : known) {
            for (Long after : known) {
                if (before.equals(after)
                        || !orderedBefore(before, after)) {
                    continue;
                }
                String direct = directKinds.get(before + ">" + after);
                JsonObject edge = new JsonObject();
                edge.addProperty("beforeEventId", before);
                edge.addProperty("afterEventId", after);
                edge.addProperty("edgeKind", direct == null
                        ? TRANSITIVE : direct);
                edge.addProperty("direct", direct != null);
                relation.add(edge);
            }
        }
        return relation;
    }

    /** The projected relation as one artifact-ready object. */
    public JsonObject toJson(Collection<Long> selected) {
        JsonArray relation = new JsonArray();
        for (JsonObject edge : project(selected)) relation.add(edge);
        JsonObject domain = new JsonObject();
        domain.addProperty("schemaVersion", 1);
        domain.addProperty("kind", "SESSION_ORDER_DOMAIN");
        domain.addProperty("authority",
                SharedStateEvidence.RECORD_AUTHORITY);
        domain.addProperty("open", open);
        domain.addProperty("partialOrder", true);
        domain.addProperty("eventCount", events.size());
        domain.add("order", relation);
        return domain;
    }
}
