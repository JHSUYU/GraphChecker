package edu.uva.liftlab.graphchecker.contract;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public final class ClientProgramOrder {
    private final Map<String, ContextShape.Stance> senders =
            new HashMap<String, ContextShape.Stance>();
    private final Map<String, Long> sent = new HashMap<String, Long>();
    private final Map<String, String> answered =
            new HashMap<String, String>();
    private final Map<String, Long> replied = new HashMap<String, Long>();

    private ClientProgramOrder() {
    }

    public static ClientProgramOrder of(List<ScheduleEvent> schedule) {
        ClientProgramOrder order = new ClientProgramOrder();
        for (ScheduleEvent event : schedule) {
            ContextShape.Stance at = stance(event.context());
            if (at == null) continue;
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !event.endpoint().isEmpty()) {
                order.senders.putIfAbsent(event.endpoint(), at);
                order.sent.putIfAbsent(event.endpoint(), event.seq());
                if (at.context() instanceof CausalContext.Anchor
                        && Endpoint.replySite(event.site())) {
                    order.answered.putIfAbsent(event.endpoint(),
                            ((CausalContext.Anchor) at.context())
                                    .producerEndpointId());
                }
            } else if (event.kind() == ScheduleEvent.Kind.RECV) {
                String request = order.answered.get(event.received());
                ContextShape.Stance sender = request == null ? null
                        : order.senders.get(request);
                if (sender != null && sender.node().equals(at.node())) {
                    order.replied.merge(request, event.seq(), Math::min);
                }
            }
        }
        return order;
    }

    public String clientRequest(OccurrenceAddress occurrence) {
        if (occurrence == null
                || !(occurrence.context() instanceof CausalContext.Anchor)) {
            return null;
        }
        String request = ((CausalContext.Anchor) occurrence.context())
                .producerEndpointId();
        ContextShape.Stance sender = senders.get(request);
        return sender != null && client(sender) ? request : null;
    }

    public boolean repliedBefore(String earlier, String later) {
        ContextShape.Stance first = senders.get(earlier);
        ContextShape.Stance second = senders.get(later);
        Long reply = replied.get(earlier);
        Long send = sent.get(later);
        return first != null && second != null
                && first.render().equals(second.render())
                && reply != null && send != null && reply < send;
    }

    public String said(String earlier, String later) {
        return senders.get(earlier).render() + " received the reply to "
                + earlier + " (schedule row " + replied.get(earlier)
                + ") before it sent " + later + " (row " + sent.get(later)
                + ")";
    }

    private static boolean client(ContextShape.Stance stance) {
        return stance.context() instanceof CausalContext.Root
                && ((CausalContext.Root) stance.context()).role()
                .equals(Role.CLIENT);
    }

    private static ContextShape.Stance stance(String context) {
        try {
            return ContextShape.Stance.ofSend(context);
        } catch (IllegalArgumentException unnamed) {
            return null;
        }
    }
}
