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
 *
 * <p>LOCK ORDER: {@code Interactions} then {@link InteractionRefusals},
 * NEVER the reverse.  Both classes guard their store with their own class
 * monitor and each calls into the other, so the pair has exactly one safe
 * order and it is this one: a thread may hold the {@code Interactions}
 * monitor and take the {@code InteractionRefusals} monitor -- which is what
 * {@link #sent} and {@link #sharedProducer} do -- and a thread inside
 * {@code InteractionRefusals} must own nothing of its own when it calls back
 * here.  The reverse edge was real: {@code InteractionRefusals.filedProducers}
 * was {@code synchronized} and delegated to {@link #filedProducers}, so a
 * refusal being rendered on the main thread and a DataNode heartbeat inside
 * {@link #sharedProducer} deadlocked on the two class monitors (thread dump
 * deadlock-21177cdb: "Found one Java-level deadlock", 11741 campaign #4,
 * which held wave 1 open until the campaign's own wall clock ran out).</p>
 */
public final class Interactions {
    /** Bounded: a long run must not retain every message it ever sent. */
    static final int LIMIT = 8192;

    private static final Map<String, Endpoint> PRODUCERS =
            new LinkedHashMap<String, Endpoint>(64, 0.75f, false) {
                @Override
                protected boolean removeEldestEntry(
                        Map.Entry<String, Endpoint> eldest) {
                    return size() > LIMIT;
                }
            };
    private Interactions() {
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
     * The producer endpoint this delivery was paired with, or null, and the
     * key that answered.
     *
     * <p>Two keys are recorded facts and they are not equal evidence: the VM
     * handle is the export itself, the correlation with the port is the
     * message the export travelled in.  Which of the two answered was not
     * stated anywhere, so an attach row paired on the weaker key read
     * exactly like one paired on the handle -- on the 11741 corpus all 3,554
     * attaches had both available.  The pairing now carries its key; the
     * attach row's own member for it belongs to the contract.</p>
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
     * The keys one delivery is paired on: the VM expression handle, and the
     * exchange correlation with the port.
     *
     * <p>Both are RECORDED facts of the run -- the VM handed out the handle
     * and the workload named the correlation -- which is the whole rule
     * (INTERACTION-ID SS1).  "The port's last producer" used to stand behind
     * them, and it is a guess: two sends on one port with no handle and no
     * correlation pair the second delivery to the first producer, and the
     * row then states a chain nobody made.  A delivery these two do not
     * pair publishes an unpaired row and LINEAGE_LOST beside it, which is
     * what {@link RowRuntime#attachedAt} does.</p>
     */
    private static java.util.List<String> keys(String portId, long handle,
                                               String correlationId) {
        String port = Text.safe(portId);
        String correlation = Text.safe(correlationId);
        java.util.List<String> keys = new java.util.ArrayList<String>(2);
        if (handle > 0L) keys.add("H\n" + handle);
        if (!correlation.isEmpty() && !port.isEmpty()) {
            keys.add("C\n" + correlation + "\n" + port);
        }
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
                                         Endpoint producer) {
        String key = message(transport, correlationId, half);
        if (key.isEmpty() || producer == null) return;
        MESSAGES.put(key, producer);
        InteractionRefusals.noteMessage(key, producer);
    }

    /**
     * The OTHER message this producer endpoint already named, or {@code ""}.
     *
     * <p>The key is this store's spelling, so it is built here; what a
     * collision MEANS, and the index that answers it, are
     * {@link InteractionRefusals}'s -- nothing on the delivery path asks
     * this question.</p>
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
    static synchronized java.util.Collection<Endpoint> filedProducers() {
        return new java.util.ArrayList<Endpoint>(MESSAGES.values());
    }

    private static String message(String transport, String correlationId,
                                  String half) {
        String correlation = Text.safe(correlationId);
        if (correlation.isEmpty()) return "";
        return Text.safe(transport) + "\n" + correlation + "\n"
                + Text.safe(half);
    }

    private static final Map<String, Endpoint> MESSAGES =
            new LinkedHashMap<String, Endpoint>(64, 0.75f, false) {
                @Override
                protected boolean removeEldestEntry(
                        Map.Entry<String, Endpoint> eldest) {
                    return size() > LIMIT;
                }
            };

    /**
     * Clears both stores.
     *
     * <p>Takes the two monitors in the declared order -- this one, then
     * {@link InteractionRefusals}'s -- so it is one more edge of the same
     * direction and cannot close a cycle.</p>
     */
    public static synchronized void resetForTests() {
        MESSAGES.clear();
        InteractionRefusals.resetForTests();
        DELIVERY.remove();
        PRODUCERS.clear();
    }
}
