package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class Interactions {
    static final int LIMIT = 8192;

    private static final Map<String, Endpoint> PRODUCERS = bounded();

    private Interactions() {
    }

    static <V> Bounded<V> bounded() {
        return new Bounded<V>();
    }

    static final class Bounded<V> extends LinkedHashMap<String, V> {
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

        long evicted() {
            return evicted;
        }
    }

    public static synchronized void exported(long handle, Endpoint producer) {
        if (producer == null || handle <= 0L) return;
        PRODUCERS.put(handleKey(handle), producer);
    }

    public static synchronized void carried(String portId,
                                            String correlationId, String half,
                                            Endpoint producer) {
        String key = messageKey(portId, correlationId, half);
        if (producer == null || key.isEmpty()) return;
        PRODUCERS.put(key, producer);
    }

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

    public static final class Pairing {
        private final Endpoint producer;
        private final String key;

        private Pairing(Endpoint producer, String key) {
            this.producer = producer;
            this.key = key;
        }

        public Endpoint producer() {
            return producer;
        }

        public String key() {
            return key;
        }
    }

    private static String handleKey(long handle) {
        return "H\n" + handle;
    }

    private static String messageKey(String portId, String correlationId,
                                     String half) {
        String port = trimmed(portId);
        String correlation = trimmed(correlationId);
        if (correlation.isEmpty() || port.isEmpty()) return "";
        return "C\n" + correlation + "\n"
                + trimmed(half).toUpperCase(Locale.ROOT) + "\n" + port;
    }

    private static final ThreadLocal<Delivery> DELIVERY =
            new ThreadLocal<Delivery>();

    public static void delivering(long handle, String correlationId,
                                  String half) {
        DELIVERY.set(new Delivery(handle, trimmed(correlationId),
                trimmed(half)));
    }

    public static void deliveringAt(long attachEventId) {
        Delivery delivery = DELIVERY.get();
        if (delivery != null) delivery.seq = attachEventId;
    }

    public static void delivered() {
        DELIVERY.remove();
    }

    public static Delivery delivery() {
        Delivery delivery = DELIVERY.get();
        return delivery == null ? Delivery.NONE : delivery;
    }

    public static final class Delivery {
        private static final Delivery NONE = new Delivery(0L, "", "");
        public final long handle;
        public final String correlationId;
        public final String half;
        private long seq;

        private Delivery(long handle, String correlationId, String half) {
            this.handle = handle;
            this.correlationId = correlationId;
            this.half = half;
        }

        public long seq() {
            return seq;
        }
    }

    public static synchronized void sent(String transport,
                                         String correlationId, String half,
                                         Endpoint producer) {
        String key = message(transport, correlationId, half);
        if (key.isEmpty() || producer == null) return;
        MESSAGES.put(key, producer);
        SENDERS.put(producer.id(), producer);
        InteractionRefusals.noteMessage(key, producer);
    }

    public static synchronized String sharedProducer(String transport,
                                                     String correlationId,
                                                     String half,
                                                     Endpoint producer) {
        if (producer == null) return "";
        return InteractionRefusals.otherMessageOf(producer.id(),
                message(transport, correlationId, half));
    }

    public static synchronized String sender(String transport,
                                             String correlationId,
                                             String half) {
        Endpoint producer = MESSAGES.get(
                message(transport, correlationId, half));
        return producer == null ? "" : producer.id();
    }

    static synchronized long sendersEvicted() {
        return MESSAGES.evicted();
    }

    public static synchronized Endpoint producer(String endpointId) {
        return SENDERS.get(trimmed(endpointId));
    }

    static synchronized Collection<Endpoint> filedProducers() {
        return new ArrayList<Endpoint>(MESSAGES.values());
    }

    private static String message(String transport, String correlationId,
                                  String half) {
        String correlation = trimmed(correlationId);
        if (correlation.isEmpty()) return "";
        return trimmed(transport) + "\n" + correlation + "\n"
                + trimmed(half);
    }

    private static final Bounded<Endpoint> MESSAGES = bounded();
    private static final Map<String, Endpoint> SENDERS = bounded();
}
