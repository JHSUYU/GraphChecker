package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import java.util.Map;

/**
 * What a refusal about a WIRE interaction must be able to say; nothing a
 * pairing ({@link Interactions}) needs.  Off the delivery path, so
 * {@link #endpoint} may scan.
 *
 * <p>LOCK ORDER: {@link Interactions} then {@code InteractionRefusals},
 * NEVER the reverse.  A method here that calls into {@code Interactions}
 * must not be {@code synchronized}; that reverse edge once deadlocked a
 * replay against a heartbeat.</p>
 */
final class InteractionRefusals {
    private InteractionRefusals() {
    }

    /**
     * The first message each producer endpoint id was minted for; bounded
     * like {@link Interactions}'s store, and never answers a pairing.
     */
    private static final Map<String, String> MESSAGE_OF_ENDPOINT =
            Interactions.bounded();

    static synchronized void noteMessage(String messageKey,
                                         Endpoint producer) {
        if (!MESSAGE_OF_ENDPOINT.containsKey(producer.id())) {
            MESSAGE_OF_ENDPOINT.put(producer.id(), messageKey);
        }
    }

    /**
     * The OTHER message this producer endpoint already named, or {@code ""}.
     * One event sends one message, so a second one means the identity failed
     * to separate two events.
     */
    static synchronized String otherMessageOf(String endpointId,
                                              String mine) {
        String first = MESSAGE_OF_ENDPOINT.get(endpointId);
        return first == null || first.equals(mine) || mine.isEmpty()
                ? "" : rendered(first);
    }

    /** One message key, as a refusal can print it. */
    private static String rendered(String key) {
        String[] parts = key.split("\n", -1);
        if (parts.length < 3) return key;
        return parts[0] + " " + parts[2] + " " + parts[1];
    }

    /**
     * The components behind one producer endpoint id, or {@code ""}: an
     * anchor digest alone tells a reader nothing.  Renders the filed
     * {@link Endpoint} from {@link Identity#endpointAt}, not a recomputation.
     */
    static String components(String endpointId) {
        Endpoint producer = endpoint(endpointId);
        return producer == null ? "" : producer.render();
    }

    /**
     * The filed endpoint {@code endpointId} was minted from, or null.  NOT
     * {@code synchronized}: the lock order above.
     */
    static Endpoint endpoint(String endpointId) {
        String id = Text.safe(endpointId);
        if (id.isEmpty()) return null;
        for (Endpoint producer : Interactions.filedProducers()) {
            if (id.equals(producer.id())) return producer;
        }
        return null;
    }

    /** Called with the {@link Interactions} monitor held: declared order. */
    static synchronized void resetForTests() {
        MESSAGE_OF_ENDPOINT.clear();
    }
}
