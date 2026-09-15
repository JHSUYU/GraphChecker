package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The within-run pairing evidence of a WIRE interaction: which export an
 * attach took its value from.
 *
 * <p>INTERACTION-ID §1: within one run the pairing is a recorded fact --
 * the exchange correlation id and the expression handle.  The producer
 * files its endpoint here when it stages the value; the consumer asks for
 * it when it mints, and a consumer that finds nothing publishes an unpaired
 * row rather than guessing a producer.</p>
 */
public final class Interactions {
    /** Bounded: a long run must not retain every message it ever sent. */
    private static final int LIMIT = 8192;

    private static final Map<String, Endpoint> PRODUCERS =
            new LinkedHashMap<String, Endpoint>(64, 0.75f, false) {
                @Override
                protected boolean removeEldestEntry(
                        Map.Entry<String, Endpoint> eldest) {
                    return size() > LIMIT;
                }
            };
    private static final Map<String, String> EXPRESSIONS =
            new LinkedHashMap<String, String>(64, 0.75f, false) {
                @Override
                protected boolean removeEldestEntry(
                        Map.Entry<String, String> eldest) {
                    return size() > LIMIT;
                }
            };

    private Interactions() {
    }

    /** Files the producer of one staged value, by handle and by port. */
    public static synchronized void exported(String portId, long handle,
                                             String correlationId,
                                             Endpoint producer,
                                             String expressionRef) {
        if (producer == null) return;
        for (String key : keys(portId, handle, correlationId)) {
            PRODUCERS.put(key, producer);
            if (!Text.safe(expressionRef).isEmpty()) {
                EXPRESSIONS.put(key, Text.safe(expressionRef));
            }
        }
    }

    /** The producer endpoint this delivery was paired with, or null. */
    public static synchronized Endpoint producer(String portId, long handle,
                                                 String correlationId) {
        for (String key : keys(portId, handle, correlationId)) {
            Endpoint producer = PRODUCERS.get(key);
            if (producer != null) return producer;
        }
        return null;
    }

    /** The producer's expression ref for this delivery, or {@code ""}. */
    public static synchronized String expressionRef(String portId,
                                                    long handle,
                                                    String correlationId) {
        for (String key : keys(portId, handle, correlationId)) {
            String ref = EXPRESSIONS.get(key);
            if (ref != null) return ref;
        }
        return "";
    }

    /**
     * The keys one delivery can be paired on, strongest first: the VM
     * expression handle, then the exchange correlation and port, then the
     * port's last producer.
     */
    private static java.util.List<String> keys(String portId, long handle,
                                               String correlationId) {
        String port = Text.safe(portId);
        String correlation = Text.safe(correlationId);
        java.util.List<String> keys = new java.util.ArrayList<String>(3);
        if (handle > 0L) keys.add("H\n" + handle);
        if (!correlation.isEmpty() && !port.isEmpty()) {
            keys.add("C\n" + correlation + "\n" + port);
        }
        if (!port.isEmpty()) keys.add("P\n" + port);
        return keys;
    }

    /**
     * The delivery this thread is attaching, by the handle the producer
     * staged.
     *
     * <p>The mint happens four frames below the decode that took the
     * element, and the handle is the strongest pairing evidence there is
     * (INTERACTION-ID §1).  Held here for the length of one attach instead
     * of threaded through every signature between the two.</p>
     */
    private static final ThreadLocal<long[]> DELIVERY =
            new ThreadLocal<long[]>();

    public static void delivering(long handle) {
        DELIVERY.set(new long[] {handle, 0L});
    }

    /** States the VM ledger entry this delivery was attached at. */
    public static void deliveringAt(long attachEventId) {
        long[] delivery = DELIVERY.get();
        if (delivery != null) delivery[1] = attachEventId;
    }

    public static void delivered() {
        DELIVERY.remove();
    }

    /** The handle of the delivery being attached on this thread, or 0. */
    public static long deliveryHandle() {
        long[] delivery = DELIVERY.get();
        return delivery == null ? 0L : delivery[0];
    }

    /** The VM event id of that attach, or 0: the row's place in the run. */
    public static long deliverySeq() {
        long[] delivery = DELIVERY.get();
        return delivery == null ? 0L : delivery[1];
    }

    /**
     * Files the endpoint of one whole MESSAGE, for the anchor its receiver
     * will state.
     *
     * <p>A declared port's leaf is paired by handle; a request's causal
     * anchor is the message, which may carry no declared leaf at all.  Both
     * are the producer's endpoint -- this one is the exchange itself.</p>
     */
    public static synchronized void sent(String transport,
                                         String correlationId, String half,
                                         String producerEndpointId) {
        String key = message(transport, correlationId, half);
        if (key.isEmpty() || Text.safe(producerEndpointId).isEmpty()) return;
        MESSAGES.put(key, Text.safe(producerEndpointId));
    }

    /** The endpoint that sent this message, or {@code ""}. */
    public static synchronized String sender(String transport,
                                             String correlationId,
                                             String half) {
        String id = MESSAGES.get(message(transport, correlationId, half));
        return id == null ? "" : id;
    }

    private static String message(String transport, String correlationId,
                                  String half) {
        String correlation = Text.safe(correlationId);
        if (correlation.isEmpty()) return "";
        return Text.safe(transport) + "\n" + correlation + "\n"
                + Text.safe(half);
    }

    private static final Map<String, String> MESSAGES =
            new LinkedHashMap<String, String>(64, 0.75f, false) {
                @Override
                protected boolean removeEldestEntry(
                        Map.Entry<String, String> eldest) {
                    return size() > LIMIT;
                }
            };

    public static synchronized void resetForTests() {
        MESSAGES.clear();
        DELIVERY.remove();
        PRODUCERS.clear();
        EXPRESSIONS.clear();
    }
}
