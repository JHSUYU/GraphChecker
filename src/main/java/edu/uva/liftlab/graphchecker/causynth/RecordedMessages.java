package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class RecordedMessages {
    private final Map<String, String> senders = new HashMap<>();
    private final Map<String, ContextShape.Stance> stances = new HashMap<>();
    private final Map<String, Set<String>> receivers = new HashMap<>();
    private final Map<String, Set<String>> takenIn = new HashMap<>();
    private final Map<String, Set<String>> receivingStances = new HashMap<>();
    private final Map<String, Set<String>> handlers = new HashMap<>();
    private final Map<String, Set<String>> sent = new HashMap<>();
    private final Map<String, Set<String>> replies = new HashMap<>();

    RecordedMessages(Collection<ScheduleEvent> schedule) {
        for (ScheduleEvent event : schedule) {
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !event.endpoint().isEmpty()) {
                ContextShape.Stance stance =
                        ContextShape.Stance.ofSend(event.context());
                if (stance != null) stances.put(event.endpoint(), stance);
                if (!event.occurrence().isEmpty()) {
                    senders.put(event.endpoint(), event.occurrence());
                    sent.computeIfAbsent(event.occurrence(),
                            ignored -> new LinkedHashSet<>())
                            .add(event.endpoint());
                }
                if (stance != null
                        && stance.context() instanceof CausalContext.Anchor
                        && Endpoint.replySite(event.site())) {
                    replies.computeIfAbsent(((CausalContext.Anchor)
                            stance.context()).producerEndpointId(),
                            ignored -> new LinkedHashSet<>())
                            .add(event.endpoint());
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
                    (at.context() instanceof CausalContext.Anchor ? handlers
                            : receivingStances).computeIfAbsent(message,
                            ignored -> new LinkedHashSet<>())
                            .add(at.render());
                }
            }
        }
    }

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

    Set<String> replyLegsOf(OccurrenceAddress occurrence,
                            Collection<String> recorded,
                            Map<String, List<String>> readers) {
        Set<String> legs = new LinkedHashSet<>();
        Deque<String> pending = new ArrayDeque<>();
        pending.add(occurrence.id());
        for (String other : recorded) {
            OccurrenceAddress at = OccurrenceAddress.parse(other);
            if (at.standsUnder(occurrence)) pending.add(at.id());
        }
        while (!pending.isEmpty()) {
            for (String request : sent.getOrDefault(pending.poll(),
                    Collections.<String>emptySet())) {
                for (String reply : replies.getOrDefault(request,
                        Collections.<String>emptySet())) {
                    for (String reader : readers.getOrDefault(reply,
                            Collections.<String>emptyList())) {
                        if (!reader.equals(occurrence.id())
                                && legs.add(reader)) {
                            pending.add(reader);
                        }
                    }
                }
            }
        }
        return legs;
    }

    Set<String> sendersOf(OccurrenceAddress occurrence) {
        Set<String> found = new LinkedHashSet<>();
        for (String endpoint : startedBy(occurrence)) {
            String sender = senders.get(endpoint);
            if (sender != null && !sender.equals(occurrence.id())) {
                found.add(sender);
            }
        }
        return found;
    }

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

    Set<String> handlerStancesOf(OccurrenceAddress occurrence) {
        Set<String> stances = new LinkedHashSet<>();
        for (String endpoint : startedBy(occurrence)) {
            stances.addAll(handlers.getOrDefault(endpoint,
                    Collections.<String>emptySet()));
        }
        return stances;
    }

    private Set<String> startedBy(OccurrenceAddress occurrence) {
        return occurrence.context() instanceof CausalContext.Anchor
                ? Collections.singleton(((CausalContext.Anchor)
                        occurrence.context()).producerEndpointId())
                : takenIn.getOrDefault(
                        ContextShape.Stance.of(occurrence).render(),
                        Collections.<String>emptySet());
    }

    List<String> shape(CausalContext context) {
        return ContextShape.of(context, stances::get);
    }
}
