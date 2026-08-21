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
 * The one order domain, read back from the session's event ledger.
 *
 * <p>Every causal channel the VM recorded - program order, synchronization,
 * read-from, value handoff, region and admitted candidate edges - lives in
 * this single relation over one event-id space. A field version id <em>is</em>
 * an event id, so a write, a read, a lifecycle event, an RPC handoff and a
 * region entry are all directly comparable here. That is what the composer
 * needs and what per-channel position variables cannot express: two events on
 * different channels have no relation at all unless one relation holds
 * both.</p>
 *
 * <p>The domain stays partial. Unrelated events remain unrelated, nothing
 * here linearizes it, and there is deliberately no way to ask it for a
 * schedule. What it does answer is (a) whether one event provably precedes
 * another, (b) the relation restricted to a chosen set of events, and (c)
 * whether a proposed candidate order can be admitted without closing a
 * cycle - the same three questions the VM's own ledger answers, with the same
 * refusal vocabulary, because a Java-side answer that disagreed with the VM
 * would be worse than no answer.</p>
 *
 * <p>The one thing it does not take on trust is that the delivered relation
 * is the partial order the envelope says it is. Acyclicity is recomputed over
 * the edges that actually arrived, across every channel at once, and a
 * relation that closes a cycle yields the empty domain with a named
 * {@link #fault()} rather than answers nobody could rely on.</p>
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
    public static SessionOrderDomain empty() {
        return empty("");
    }

    private static SessionOrderDomain empty(String fault) {
        return new SessionOrderDomain(false, fault,
                Collections.<Long, JsonObject>emptyMap(),
                new LinkedHashMap<Long, Set<Long>>(),
                new LinkedHashMap<String, String>());
    }

    /**
     * Reads one admitted ledger record, or the envelope inside it. A record
     * that does not pass {@link SharedStateEvidence} admission yields the
     * empty domain: an unchecked relation is not an order.
     *
     * <p>Acyclicity is <em>recomputed</em> here rather than read off the
     * envelope's own flag. The flag is the VM's claim about the relation it
     * maintained; the relation that arrives is the one this composition will
     * reason over, and a claim that does not hold of the delivered edges is
     * exactly the case a consumer must not be allowed to walk. Program order,
     * synchronization, read-from and value handoff all live in this one
     * relation, so the check is also the cross-channel cycle check: a cycle
     * that closes only through an RPC handoff edge is refused here and never
     * reaches the formula.</p>
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

    /**
     * Names one cycle of the delivered relation, or "" when it has none.
     *
     * <p>The walk is over the whole relation at once, which is the point: the
     * channels are not separate graphs here, so a field write ordered before a
     * read that is ordered before a handoff attach that is ordered before that
     * same write is found by the same traversal as a single-channel cycle.</p>
     */
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

    /**
     * Why this domain holds no relation, or "" when it holds one.
     *
     * <p>A refusal and an empty session are different findings and a consumer
     * must be able to tell them apart: the first says the recorded order was
     * unusable, the second says nothing was recorded.</p>
     */
    public String fault() {
        return fault;
    }

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
    public boolean open() {
        return open;
    }

    public boolean isEmpty() {
        return events.isEmpty();
    }

    public int eventCount() {
        return events.size();
    }

    public boolean knows(long eventId) {
        return events.containsKey(eventId);
    }

    /** The declared kind of one event, or "" when it is not recorded. */
    public String eventKind(long eventId) {
        return string(events.get(eventId), "eventKind");
    }

    /** The region occurrence one event belongs to, or "". */
    public String regionOf(long eventId) {
        return string(events.get(eventId), "regionId");
    }

    public long contextOf(long eventId) {
        return longInteger(events.get(eventId), "contextId", 0L);
    }

    /** The synchronization object one event acted on, or 0. */
    public long objectOf(long eventId) {
        return longInteger(events.get(eventId), "objectSymRid", 0L);
    }

    /** Every recorded event, ascending. */
    public Set<Long> eventIds() {
        return Collections.unmodifiableSet(new TreeSet<>(events.keySet()));
    }

    /**
     * Whether {@code before} provably precedes {@code after} in the recorded
     * relation, directly or through other events. Unrelated is not "after":
     * a false answer here means the run showed no order, never that the
     * opposite order held.
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

    /**
     * The kind of the edge the ledger recorded directly between two events,
     * or "" when it recorded none. A read-from edge exists only where the VM
     * proved the provenance; a guarded read draws none, deliberately, so this
     * is the check that separates a proven equality from an undecided one.
     */
    public String directKind(long before, long after) {
        String kind = directKinds.get(before + ">" + after);
        return kind == null ? "" : kind;
    }

    /**
     * Every edge the ledger recorded directly, in insertion order.  A pair
     * appears once, under the first kind it was recorded with.
     */
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
     * Offers one candidate order edge, with the ledger's own semantics: a
     * self edge, an unknown event and a cyclic proposal are all refused, and
     * nothing is added when they are. An admitted candidate joins the same
     * relation as every observed edge, so a later proposal is checked against
     * it too.
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
     * The relation restricted to {@code selected}: one row per ordered pair
     * of selected events, whether the ledger related them directly or through
     * events the slice does not keep.
     *
     * <p>Restricting by reachability rather than by direct edges is what
     * makes the projection sound. Two selected writes may be ordered only
     * through an intermediate lifecycle, volatile, or handoff event the slice
     * does not retain; dropping that pair would report them as concurrent.</p>
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
