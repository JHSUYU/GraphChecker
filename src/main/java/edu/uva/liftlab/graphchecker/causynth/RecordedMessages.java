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
 * and the occurrences that took it in (each RECV under its anchor).  What
 * PLAN asks of them: the doors of the message that started an occurrence
 * ({@link #doorsOf}), and a context's shape ({@link #shape}), the same rule
 * EXPLORE reads off its corpus ({@code explore.Corpus#contextShape}).
 */
final class RecordedMessages {
    /** Producer endpoint id -> the occurrence id that sent the message. */
    private final Map<String, String> senders = new HashMap<>();
    /** Producer endpoint id -> where its SEND stood. */
    private final Map<String, ContextShape.Stance> stances = new HashMap<>();
    /** Producer endpoint id -> the occurrence ids that took it in. */
    private final Map<String, Set<String>> receivers = new HashMap<>();

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
            } else if (event.kind() == ScheduleEvent.Kind.RECV
                    && !event.occurrence().isEmpty()) {
                // "node|Anchor:<producer endpoint>@<site>[|...]"
                String[] stance = event.context().split("\\|", -1);
                CausalContext context = CausalContext.parse(
                        stance.length < 2 ? stance[0] : stance[1]);
                if (context instanceof CausalContext.Anchor) {
                    receivers.computeIfAbsent(((CausalContext.Anchor) context)
                            .producerEndpointId(),
                            ignored -> new LinkedHashSet<>())
                            .add(event.occurrence());
                }
            }
        }
    }

    /**
     * The occurrence ids at the doors of the message that started {@code
     * occurrence}: its sender, and every occurrence that took it in.  None
     * when its context is no {@code Anchor}.
     */
    Set<String> doorsOf(OccurrenceAddress occurrence) {
        if (!(occurrence.context() instanceof CausalContext.Anchor)) {
            return Collections.emptySet();
        }
        String endpoint = ((CausalContext.Anchor) occurrence.context())
                .producerEndpointId();
        Set<String> doors = new LinkedHashSet<>(receivers.getOrDefault(
                endpoint, Collections.<String>emptySet()));
        String sender = senders.get(endpoint);
        if (sender != null) doors.add(sender);
        doors.remove(occurrence.id());
        return doors;
    }

    /** The shape of {@code context} over the recording's senders. */
    List<String> shape(CausalContext context) {
        return ContextShape.of(context, stances::get);
    }
}
