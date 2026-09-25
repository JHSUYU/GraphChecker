package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Within-run pairing evidence of a WIRE interaction: which export an attach
 * took its value from.  Pairing is a recorded fact (INTERACTION-ID §1); a
 * consumer that finds nothing publishes an unpaired row, never a guess.
 *
 * <p>LOCK ORDER: {@code Interactions} then {@link InteractionRefusals},
 * never the reverse.  A thread inside {@code InteractionRefusals} must hold
 * nothing of its own when it calls back here; the reverse edge once
 * deadlocked a replay.</p>
 */
public final class Interactions {
    /** Bounded: a long run must not retain every message it ever sent. */
    static final int LIMIT = 8192;

    private static final Map<String, Endpoint> PRODUCERS = bounded();

    private Interactions() {
    }

    /** An insertion-ordered store that drops its eldest past {@link #LIMIT}. */
    static <V> Map<String, V> bounded() {
        return new LinkedHashMap<String, V>(64, 0.75f, false) {
            @Override
            protected boolean removeEldestEntry(Map.Entry<String, V> eldest) {
                return size() > LIMIT;
            }
        };
    }

    /** Files the producer of one staged value, by every key it states. */
    public static synchronized void exported(String portId, long handle,
                                             String correlationId,
                                             Endpoint producer) {
        if (producer == null) return;
        for (String key : keys(portId, handle, correlationId)) {
            PRODUCERS.put(key, producer);
        }
    }

    /**
     * The producer this delivery was paired with (or null) and the key that
     * answered: the handle (the export itself) is stronger evidence than the
     * correlation-with-port (the message it travelled in).
     */
    public static synchronized Pairing pairing(String portId, long handle,
                                               String correlationId) {
        for (String key : keys(portId, handle, correlationId)) {
            Endpoint producer = PRODUCERS.get(key);
            if (producer != null) {
                return new Pairing(producer, key.charAt(0) == 'H'
                        ? "HANDLE" : "CORRELATION_PORT");
            }
        }
        return new Pairing(null, "");
    }

    /** One delivery's producer and the key that named it. */
    public static final class Pairing {
        private final Endpoint producer;
        private final String key;

        private Pairing(Endpoint producer, String key) {
            this.producer = producer;
            this.key = key;
        }

        /** The producer endpoint, or null when neither key answered. */
        public Endpoint producer() {
            return producer;
        }

        /** {@code HANDLE}, {@code CORRELATION_PORT}, or {@code ""}. */
        public String key() {
            return key;
        }
    }

    /**
     * The pairing keys: the VM handle and the correlation with the port, both
     * recorded facts (INTERACTION-ID §1).  Never "the port's last producer",
     * which is a guess; unpaired deliveries go to {@link RowRuntime#attachedAt}.
     */
    private static List<String> keys(String portId, long handle,
                                     String correlationId) {
        String port = Text.safe(portId);
        String correlation = Text.safe(correlationId);
        List<String> keys = new ArrayList<String>(2);
        if (handle > 0L) keys.add("H\n" + handle);
        if (!correlation.isEmpty() && !port.isEmpty()) {
            keys.add("C\n" + correlation + "\n" + port);
        }
        return keys;
    }

    /**
     * The delivery this thread is attaching ({handle, attach event id}), held
     * for one attach because the mint runs frames below the decode.
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
     * Files the endpoint of one whole MESSAGE: a request's causal anchor,
     * which may carry no declared leaf to pair by handle.
     */
    public static synchronized void sent(String transport,
                                         String correlationId, String half,
                                         Endpoint producer) {
        String key = message(transport, correlationId, half);
        if (key.isEmpty() || producer == null) return;
        MESSAGES.put(key, producer);
        InteractionRefusals.noteMessage(key, producer);
    }

    /**
     * The OTHER message this producer already named, or {@code ""}; the
     * meaning of a collision is {@link InteractionRefusals}'s.
     */
    public static synchronized String sharedProducer(String transport,
                                                     String correlationId,
                                                     String half,
                                                     Endpoint producer) {
        if (producer == null) return "";
        return InteractionRefusals.otherMessageOf(producer.id(),
                message(transport, correlationId, half));
    }

    /** The endpoint that sent this message, or {@code ""}. */
    public static synchronized String sender(String transport,
                                             String correlationId,
                                             String half) {
        Endpoint producer = MESSAGES.get(
                message(transport, correlationId, half));
        return producer == null ? "" : producer.id();
    }

    /** The producers this run has filed, for a refusal to search. */
    static synchronized Collection<Endpoint> filedProducers() {
        return new ArrayList<Endpoint>(MESSAGES.values());
    }

    private static String message(String transport, String correlationId,
                                  String half) {
        String correlation = Text.safe(correlationId);
        if (correlation.isEmpty()) return "";
        return Text.safe(transport) + "\n" + correlation + "\n"
                + Text.safe(half);
    }

    private static final Map<String, Endpoint> MESSAGES = bounded();

    /** Clears both stores, taking the monitors in the declared order. */
    public static synchronized void resetForTests() {
        MESSAGES.clear();
        InteractionRefusals.resetForTests();
        DELIVERY.remove();
        PRODUCERS.clear();
    }
}
