package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionReader;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * The epoch's skeleton: which interactions have a slot (R-I6).
 *
 * <p>A SLOT is an interaction identity in this epoch's skeleton, and a
 * family is the arms of one slot.  Rows from any replay, any worker and any
 * wave fall into slots by the two endpoint ids alone, which is what lets
 * parallel workers fill them independently and lets merging be per slot.</p>
 *
 * <p>Growth is the normal case and is not an event: a pair no slot covers
 * yet is one exploration has not opened, and the composition says so and
 * carries on.  What forks an epoch is REPLACEMENT -- a consumer endpoint
 * already in a slot paired with a DIFFERENT producer endpoint.  That is a
 * contradiction and not growth: the two pairings cannot both be this
 * epoch's, so the replacing session's rows do not fill this epoch's
 * families, and the composition refuses rather than merging two
 * topologies.</p>
 */
public final class SlotTable {
    /** The file the explore stage writes beside an iteration's sessions. */
    public static final String FILE = "slots.jsonl";

    /** Consumer endpoint id -> the producer this epoch's skeleton pairs it
     *  with. */
    private final Map<String, String> producerByConsumer;
    /** Consumer endpoint id -> the session that opened its slot. */
    private final Map<String, String> openedBy;
    private final boolean stated;

    private SlotTable(Map<String, String> producerByConsumer,
                      Map<String, String> openedBy, boolean stated) {
        this.producerByConsumer = producerByConsumer;
        this.openedBy = openedBy;
        this.stated = stated;
    }

    /**
     * Reads {@code <iteration>/slots.jsonl}, or answers "no skeleton yet".
     *
     * <p>An epoch that has published no slot table has opened no slots, and
     * every pairing in the rows is then growth: the rule has nothing to
     * contradict, so it says nothing at all rather than naming every
     * interaction as unopened.</p>
     */
    public static SlotTable read(Path iteration) throws IOException {
        Path file = iteration == null ? null : iteration.resolve(FILE);
        if (file == null || !Files.isRegularFile(file)) {
            return new SlotTable(
                    Collections.<String, String>emptyMap(),
                    Collections.<String, String>emptyMap(), false);
        }
        Map<String, String> producers = new LinkedHashMap<String, String>();
        Map<String, String> opened = new LinkedHashMap<String, String>();
        for (JsonObject row : RowCodec.readJsonl(file)) {
            String consumer = endpointId(row, "consumer",
                    "consumerEndpointId");
            String producer = endpointId(row, "producer",
                    "producerEndpointId");
            if (consumer.isEmpty() || producer.isEmpty()) continue;
            producers.put(consumer, producer);
            opened.put(consumer, JsonText.firstNonBlank(
                    JsonText.string(row, "openedBySession"),
                    JsonText.string(row, "sessionId")));
        }
        return new SlotTable(producers, opened, true);
    }

    /** An endpoint stated as an id, or as the endpoint the codec reads. */
    private static String endpointId(JsonObject row, String member,
                                     String idMember) {
        String stated = JsonText.string(row, idMember);
        if (!stated.isEmpty()) return stated;
        JsonObject endpoint = JsonText.object(row, member);
        if (endpoint.size() == 0) return "";
        try {
            Endpoint read = RowCodec.readEndpoint(endpoint);
            return read == null ? "" : read.id();
        } catch (RuntimeException malformed) {
            return "";
        }
    }

    /** Whether this epoch published a skeleton at all. */
    public boolean stated() {
        return stated;
    }

    /** Whether this consumer endpoint has a slot in the skeleton. */
    public boolean opened(String consumerEndpointId) {
        return producerByConsumer.containsKey(consumerEndpointId);
    }

    /** The producer this epoch's skeleton pairs that consumer with, or "". */
    public String producerOf(String consumerEndpointId) {
        String producer = producerByConsumer.get(consumerEndpointId);
        return producer == null ? "" : producer;
    }

    /** Which session opened that slot, or "". */
    public String openedBy(String consumerEndpointId) {
        String session = openedBy.get(consumerEndpointId);
        return session == null ? "" : session;
    }

    /** One session that pairs a slot's consumer with another producer. */
    public static final class Replacement {
        public final String sessionId;
        public final String consumerEndpointId;
        public final String skeletonProducerId;
        public final String replayProducerId;
        public final String openedBySession;

        Replacement(String sessionId, String consumerEndpointId,
                    String skeletonProducerId, String replayProducerId,
                    String openedBySession) {
            this.sessionId = sessionId;
            this.consumerEndpointId = consumerEndpointId;
            this.skeletonProducerId = skeletonProducerId;
            this.replayProducerId = replayProducerId;
            this.openedBySession = openedBySession;
        }

        /** Both pairings, which is what the gap has to name. */
        public String detail() {
            return "the skeleton pairs consumer " + consumerEndpointId
                    + " with producer " + skeletonProducerId + " (slot opened"
                    + " by session " + openedBySession + ") and session "
                    + sessionId + " paired it with producer "
                    + replayProducerId + ": two pairings of one consumer are"
                    + " a replacement, not growth, so this epoch's families"
                    + " take no rows from that session";
        }
    }

    /**
     * Every replacement the corpus states, in session order.
     *
     * <p>Asked of the attach rows and nothing else: the pairing is a
     * recorded fact of the run that made it, and a replacement is two runs
     * disagreeing about it.</p>
     */
    public java.util.List<Replacement> replacements(CorpusIndex corpus) {
        java.util.List<Replacement> found =
                new java.util.ArrayList<Replacement>();
        if (!stated) return found;
        Set<String> seen = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            for (AttachRow attach : session.attaches()) {
                Endpoint producer = attach.producer();
                if (producer == null) continue;
                String consumer = attach.endpoint().id();
                if (!opened(consumer)) continue;
                String expected = producerOf(consumer);
                if (expected.equals(producer.id())) continue;
                if (!seen.add(session.sessionId() + "|" + consumer)) continue;
                found.add(new Replacement(session.sessionId(), consumer,
                        expected, producer.id(), openedBy(consumer)));
            }
        }
        return found;
    }
}
