package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;

/**
 * Within-run pairing evidence of a WIRE interaction: which export an attach
 * took its value from.  Pairing is a recorded fact (IDENTITY §4); a
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
    static <V> Bounded<V> bounded() {
        return new Bounded<V>();
    }

    /** A store bounded at {@link #LIMIT}, counting what it dropped. */
    static final class Bounded<V> extends LinkedHashMap<String, V> {
        /** Under the owner's monitor: a miss after the first drop may be one. */
        private long evicted;

        private Bounded() {
            super(64, 0.75f, false);
        }

        @Override
        protected boolean removeEldestEntry(Map.Entry<String, V> eldest) {
            if (size() <= LIMIT) return false;
            evicted++;
            return true;
        }

        @Override
        public void clear() {
            super.clear();
            evicted = 0L;
        }

        /** How many entries it dropped; under the owner's monitor. */
        long evicted() {
            return evicted;
        }
    }

    /** Files the producer of one exported value by its VM handle. */
    public static synchronized void exported(long handle, Endpoint producer) {
        if (producer == null || handle <= 0L) return;
        PRODUCERS.put(handleKey(handle), producer);
    }

    /**
     * Files the producer of one value a message carries, by that message --
     * its correlation and half -- and the port: called at the message's own
     * outbound door ({@link SymbolicMessageEnvelope#carriedBy}), never where
     * the value was exported, whose thread may be serving another message
     * (a server's export answers the request it serves in its response half,
     * never in that request's).
     */
    public static synchronized void carried(String portId,
                                            String correlationId, String half,
                                            Endpoint producer) {
        String key = messageKey(portId, correlationId, half);
        if (producer == null || key.isEmpty()) return;
        PRODUCERS.put(key, producer);
    }

    /**
     * The producer this delivery was paired with (or null) and the key that
     * answered: the handle (the export itself) is stronger evidence than the
     * message it travelled in ({@code correlationId}, {@code half}) with the
     * port, which is asked only of an element the message carried -- one it
     * did not ({@code handle} {@link SymbolicMessageEnvelope#ABSENT}) was
     * staged by no export of its sender, and pairs with nothing.
     */
    public static synchronized Pairing pairing(String portId, long handle,
                                               String correlationId,
                                               String half) {
        if (handle > 0L) {
            Endpoint producer = PRODUCERS.get(handleKey(handle));
            if (producer != null) return new Pairing(producer, "HANDLE");
        }
        if (handle >= 0L) {
            String key = messageKey(portId, correlationId, half);
            Endpoint producer = key.isEmpty() ? null : PRODUCERS.get(key);
            if (producer != null) {
                return new Pairing(producer, "CORRELATION_PORT");
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

    /*
     * The pairing keys: the VM handle, and the message (correlation and
     * half) with the port, both recorded facts (IDENTITY §4).  Never "the
     * port's last producer", which is a guess; unpaired deliveries go to
     * {@link RowRuntime#attachedAt}.
     */
    private static String handleKey(long handle) {
        return "H\n" + handle;
    }

    /** The message key of one port, or "" when the message names none. */
    private static String messageKey(String portId, String correlationId,
                                     String half) {
        String port = Text.safe(portId);
        String correlation = Text.safe(correlationId);
        if (correlation.isEmpty() || port.isEmpty()) return "";
        return "C\n" + correlation + "\n"
                + Text.safe(half).toUpperCase(Locale.ROOT) + "\n" + port;
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
        SENDERS.put(producer.id(), producer);
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

    /** How many messages {@link #sender} can no longer answer for. */
    static synchronized long sendersEvicted() {
        return MESSAGES.evicted();
    }

    /** The whole endpoint a message's anchor names, or {@code null} when
     *  this run filed no message under it. */
    public static synchronized Endpoint producer(String endpointId) {
        return SENDERS.get(Text.safe(endpointId));
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

    private static final Bounded<Endpoint> MESSAGES = bounded();
    /** The same producers, by endpoint id: what an anchor names. */
    private static final Map<String, Endpoint> SENDERS = bounded();

    /** Clears every store, taking the monitors in the declared order. */
    public static synchronized void resetForTests() {
        MESSAGES.clear();
        SENDERS.clear();
        InteractionRefusals.resetForTests();
        DELIVERY.remove();
        PRODUCERS.clear();
    }
}
