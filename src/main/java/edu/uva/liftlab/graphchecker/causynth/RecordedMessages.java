package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The messages of the recording, read off its schedule (IDENTITY §4, §8):
 * the stance each was sent from and the occurrence that sent it (its SEND),
 * and the occurrences that took it in (each RECV of it: under its anchor, or
 * into a context of the receiver's own, {@link ScheduleEvent#received}).
 * What PLAN asks of them: the doors of the message that started an
 * occurrence ({@link #doorsOf}), and a context's shape ({@link #shape}), the
 * same rules EXPLORE reads off its corpus ({@code explore.Corpus}).
 */
final class RecordedMessages {
    /** Producer endpoint id -> the occurrence id that sent the message. */
    private final Map<String, String> senders = new HashMap<>();
    /** Producer endpoint id -> where its SEND stood. */
    private final Map<String, ContextShape.Stance> stances = new HashMap<>();
    /** Producer endpoint id -> the occurrence ids that took it in. */
    private final Map<String, Set<String>> receivers = new HashMap<>();
    /** Where a context anchored on nothing stands -> the messages it took
     *  into itself (a DataNode's turn and its DataTransfer op; a batching
     *  Overseer turn, every item it flushed at once). */
    private final Map<String, Set<String>> takenIn = new HashMap<>();
    /** Producer endpoint id -> the stances of the turns that took it in at
     *  their root, no occurrence open ({@link #doorStancesOf}). */
    private final Map<String, Set<String>> receivingStances = new HashMap<>();
    /** Producer endpoint id -> the stances of the turns standing on it, its
     *  handlers ({@link #handlerStancesOf}): what it started, no door. */
    private final Map<String, Set<String>> handlers = new HashMap<>();

    RecordedMessages(Collection<ScheduleEvent> schedule) {
        for (ScheduleEvent event : schedule) {
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !event.endpoint().isEmpty()) {
                // Where every message was sent from, in a region or not: a
                // daemon tick's heartbeat is sent from the tick's root alone.
                ContextShape.Stance stance =
                        ContextShape.Stance.ofSend(event.context());
                if (stance != null) stances.put(event.endpoint(), stance);
                if (!event.occurrence().isEmpty()) {
                    senders.put(event.endpoint(), event.occurrence());
                }
            } else if (!event.received().isEmpty()) {
                String message = event.received();
                ContextShape.Stance at =
                        ContextShape.Stance.ofSend(event.context());
                if (at != null
                        && !(at.context() instanceof CausalContext.Anchor)) {
                    takenIn.computeIfAbsent(at.render(),
                            ignored -> new LinkedHashSet<>()).add(message);
                }
                if (!event.occurrence().isEmpty()) {
                    receivers.computeIfAbsent(message,
                            ignored -> new LinkedHashSet<>())
                            .add(event.occurrence());
                } else if (at != null) {
                    // Taken in at a turn's root; a turn standing on the
                    // message (a request's handler) is what it started.
                    (at.context() instanceof CausalContext.Anchor ? handlers
                            : receivingStances).computeIfAbsent(message,
                            ignored -> new LinkedHashSet<>())
                            .add(at.render());
                }
            }
        }
    }

    /**
     * The occurrence ids at the doors of the message that started {@code
     * occurrence} -- its context's anchor, else the message that context
     * took into itself: its sender, and every occurrence that took it in.
     * None when no message started it.
     */
    Set<String> doorsOf(OccurrenceAddress occurrence) {
        Set<String> doors = new LinkedHashSet<>();
        for (String endpoint : startedBy(occurrence)) {
            doors.addAll(receivers.getOrDefault(endpoint,
                    Collections.<String>emptySet()));
            String sender = senders.get(endpoint);
            if (sender != null) doors.add(sender);
        }
        doors.remove(occurrence.id());
        return doors;
    }

    /**
     * The stances of the turns whose every occurrence holds a door of the
     * message that started {@code occurrence}: the turn that sent it --
     * whatever it ran before the send, on any of its threads, a fault of
     * which can stop the turn short of it (RestoreCmd's RESTORECORE
     * requests before its ACTIVE offer) -- and each turn that took it in at
     * its root before any of its regions opened (an Overseer queue loop's
     * turn, its task item, and the ZooKeeper door a region of the turn
     * runs).
     */
    Set<String> doorStancesOf(OccurrenceAddress occurrence) {
        Set<String> doors = new LinkedHashSet<>();
        for (String endpoint : startedBy(occurrence)) {
            doors.addAll(receivingStances.getOrDefault(endpoint,
                    Collections.<String>emptySet()));
            ContextShape.Stance sentFrom = stances.get(endpoint);
            if (sentFrom != null) doors.add(sentFrom.render());
        }
        return doors;
    }

    /** The stances of the turns standing on a message that started {@code
     *  occurrence} -- its handlers, which it started: no doors of it, each
     *  cut named by its caller. */
    Set<String> handlerStancesOf(OccurrenceAddress occurrence) {
        Set<String> stances = new LinkedHashSet<>();
        for (String endpoint : startedBy(occurrence)) {
            stances.addAll(handlers.getOrDefault(endpoint,
                    Collections.<String>emptySet()));
        }
        return stances;
    }

    /** The producer endpoints of the messages that started {@code
     *  occurrence}: its context's anchor, else every message that context
     *  took into itself (a batching turn is started by each item it took
     *  in); none for none. */
    private Set<String> startedBy(OccurrenceAddress occurrence) {
        return occurrence.context() instanceof CausalContext.Anchor
                ? Collections.singleton(((CausalContext.Anchor)
                        occurrence.context()).producerEndpointId())
                : takenIn.getOrDefault(
                        ContextShape.Stance.of(occurrence).render(),
                        Collections.<String>emptySet());
    }

    /** The shape of {@code context} over the recording's senders. */
    List<String> shape(CausalContext context) {
        return ContextShape.of(context, stances::get);
    }
}
