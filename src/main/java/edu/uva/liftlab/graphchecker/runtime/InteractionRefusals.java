package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

final class InteractionRefusals {
    private InteractionRefusals() {
    }

    private static final Map<String, String> MESSAGE_OF_ENDPOINT =
            Interactions.bounded();

    static synchronized void noteMessage(String messageKey,
                                         Endpoint producer) {
        if (!MESSAGE_OF_ENDPOINT.containsKey(producer.id())) {
            MESSAGE_OF_ENDPOINT.put(producer.id(), messageKey);
        }
    }

    static synchronized String otherMessageOf(String endpointId,
                                              String mine) {
        String first = MESSAGE_OF_ENDPOINT.get(endpointId);
        return first == null || first.equals(mine) || mine.isEmpty()
                ? "" : rendered(first);
    }

    private static String rendered(String key) {
        String[] parts = key.split("\n", -1);
        if (parts.length < 3) return key;
        return parts[0] + " " + parts[2] + " " + parts[1];
    }

    static String components(String endpointId) {
        Endpoint producer = endpoint(endpointId);
        return producer == null ? "" : producer.render();
    }

    static Endpoint endpoint(String endpointId) {
        String id = trimmed(endpointId);
        if (id.isEmpty()) return null;
        for (Endpoint producer : Interactions.filedProducers()) {
            if (id.equals(producer.id())) return producer;
        }
        return null;
    }
}
