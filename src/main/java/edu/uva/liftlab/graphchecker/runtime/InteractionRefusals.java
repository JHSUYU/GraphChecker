package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What a refusal about a WIRE interaction has to be able to say, and
 * nothing a pairing needs.
 *
 * <p>Split out of {@link Interactions} because it is the other notion in
 * that file: pairing answers "which export did this attach take its value
 * from" on every delivery, and this answers "what were the components
 * behind that anchor" and "did one producer endpoint id name two messages"
 * -- questions asked only where a refusal is printed.  It also holds the
 * one O(n) scan: {@link #endpoint} walks the filed producers rather than
 * keeping a second index of them, which is affordable exactly because
 * nothing on the delivery path calls it.</p>
 */
final class InteractionRefusals {
    private InteractionRefusals() {
    }

    /**
     * The first message each producer endpoint id was minted for.
     *
     * <p>Bounded and evicted with {@link Interactions}'s own store: a run
     * that has forgotten a message has forgotten the endpoint that sent
     * it.  Not a second store of producers -- it is an index over that one,
     * keyed the other way round, and it never answers a pairing.</p>
     */
    private static final Map<String, String> MESSAGE_OF_ENDPOINT =
            new LinkedHashMap<String, String>(64, 0.75f, false) {
                @Override
                protected boolean removeEldestEntry(
                        Map.Entry<String, String> eldest) {
                    return size() > Interactions.LIMIT;
                }
            };

    /** Files the first message one producer endpoint id was minted for. */
    static synchronized void noteMessage(String messageKey,
                                         Endpoint producer) {
        if (!MESSAGE_OF_ENDPOINT.containsKey(producer.id())) {
            MESSAGE_OF_ENDPOINT.put(producer.id(), messageKey);
        }
    }

    /**
     * The OTHER message this producer endpoint already named, or {@code ""}.
     *
     * <p>An endpoint id is (occurrence, site, the k-th event of that
     * occurrence there, attempt), and one event sends one message: a second
     * message under the same id means the identity did not separate two
     * events, so both messages' consumers state one causal anchor.  Called
     * right after the mint files it, so the id's own message is the one
     * passed in and anything else under it is the collision.</p>
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
     * The components behind one producer endpoint id, as this run minted
     * them, or {@code ""}.
     *
     * <p>An anchor travels as a digest, so a refusal naming two of them
     * names nothing a reader can act on: on hdfs-17960 the endpoints behind
     * {@code Anchor:81d0aa0dbdd84d73} and {@code Anchor:5cd4981c9a67d41e}
     * agreed on their occurrence, their transport site and their attempt
     * and differed in one number, and finding that out took a brute-force
     * search over candidate components.  What comes back here is the filed
     * {@link Endpoint} itself -- the very object {@link
     * Identity#endpointAt} built from its four inputs -- so the components
     * are stated rather than computed a second time.</p>
     */
    static String components(String endpointId) {
        Endpoint producer = endpoint(endpointId);
        return producer == null ? "" : producer.render();
    }

    /**
     * The endpoint {@code endpointId} was minted from, or {@code null}.
     *
     * <p>The filed object, so a reader comparing two anchors compares the
     * four inputs themselves -- occurrence, site, site index, attempt --
     * instead of two renders of them.</p>
     */
    static Endpoint endpoint(String endpointId) {
        String id = Text.safe(endpointId);
        if (id.isEmpty()) return null;
        // Over the filed endpoints rather than a second index of them: one
        // store of producers, read on the path that prints a refusal.
        for (Endpoint producer : filedProducers()) {
            if (id.equals(producer.id())) return producer;
        }
        return null;
    }

    private static synchronized Collection<Endpoint> filedProducers() {
        return Interactions.filedProducers();
    }

    static synchronized void resetForTests() {
        MESSAGE_OF_ENDPOINT.clear();
    }
}
