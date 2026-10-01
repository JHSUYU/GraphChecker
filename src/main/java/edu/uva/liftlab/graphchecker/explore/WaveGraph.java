package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/** G_k and its growth (PIPELINE §7.1, §7.8). {@code graph.jsonl}: NODE
 *  per activated occurrence, EDGE per WIRE pairing or STATE join, with worlds
 *  ({@link ObligationFactory#worldDigest}), plus a FRONTIER diff; no THREAD
 *  edge (schedule rows carry no occurrence). {@code growth.jsonl}: the
 *  occurrences the closure demands and no session captured ({@link
 *  ClosurePlanner.Plan#exposed}). */
final class WaveGraph {
    static final String GRAPH = "graph.jsonl";
    static final String GROWTH = "growth.jsonl";

    private final Map<String, JsonObject> nodes =
            new LinkedHashMap<String, JsonObject>();
    private final Map<String, JsonObject> edges =
            new LinkedHashMap<String, JsonObject>();
    private final Map<String, Set<String>> nodeWorlds =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> edgeWorlds =
            new LinkedHashMap<String, Set<String>>();

    private WaveGraph() {
    }

    static WaveGraph of(Corpus corpus) {
        WaveGraph graph = new WaveGraph();
        for (SessionReader session : corpus.sessions()) {
            if (!session.admitted()) continue;
            String world = ObligationFactory.worldDigest(
                    corpus.world(session.sessionId()));
            for (ActivationRow activation : session.activations()) {
                graph.node(activation.occurrence(), activation.instrumented(),
                        world);
            }
            for (AttachRow attach : session.attaches()) {
                if (attach.producer() == null) continue;
                graph.edge(InteractionKind.WIRE, attach.producer(),
                        attach.endpoint(), world);
            }
            for (ReadRow read : session.reads()) {
                WriteRow write = corpus.writeOf(read.sessionId(),
                        read.location(), read.observedVersion());
                if (write == null) continue;
                graph.edge(InteractionKind.STATE, write.endpoint(),
                        read.endpoint(), world);
            }
        }
        return graph;
    }

    private void node(OccurrenceAddress occurrence, boolean instrumented,
                      String world) {
        JsonObject row = nodes.get(occurrence.id());
        if (row == null) {
            row = new JsonObject();
            row.addProperty("kind", "NODE");
            row.addProperty("occurrenceId", occurrence.id());
            row.addProperty("occurrence", occurrence.render());
            row.addProperty("node", occurrence.node().render());
            row.addProperty("regionId", occurrence.regionId());
            row.addProperty("instrumented", false);
            nodes.put(occurrence.id(), row);
            nodeWorlds.put(occurrence.id(), new TreeSet<String>());
        }
        if (instrumented) row.addProperty("instrumented", true);
        nodeWorlds.get(occurrence.id()).add(world);
    }

    private void edge(InteractionKind kind, Endpoint producer,
                      Endpoint consumer, String world) {
        String id = Interaction.of(kind, producer, consumer).id();
        JsonObject row = edges.get(id);
        if (row == null) {
            row = new JsonObject();
            row.addProperty("kind", "EDGE");
            row.addProperty("edgeId", id);
            row.addProperty("edge", kind.name());
            row.addProperty("producer", producer.render());
            row.addProperty("producerOccurrenceId",
                    producer.occurrence().id());
            row.addProperty("consumer", consumer.render());
            row.addProperty("consumerOccurrenceId",
                    consumer.occurrence().id());
            edges.put(id, row);
            edgeWorlds.put(id, new TreeSet<String>());
        }
        edgeWorlds.get(id).add(world);
    }

    /** Writes {@code graph.jsonl} with its FRONTIER against the previous
     *  round's. */
    void write(Path roundDir, int round) throws IOException {
        Set<String> before = new LinkedHashSet<String>();
        if (round > 0) {
            Path previous = roundDir.resolveSibling(
                    String.format("obligations-%04d", round - 1))
                    .resolve(GRAPH);
            if (Files.isRegularFile(previous)) {
                for (JsonObject row : RowCodec.readJsonl(previous)) {
                    if (row.has("occurrenceId")) {
                        before.add(row.get("occurrenceId").getAsString());
                    }
                    if (row.has("edgeId")) {
                        before.add(row.get("edgeId").getAsString());
                    }
                }
            }
        }
        List<JsonObject> rows = new ArrayList<JsonObject>();
        int newNodes = 0;
        int newEdges = 0;
        for (Map.Entry<String, JsonObject> node : nodes.entrySet()) {
            node.getValue().add("worlds",
                    ExploreCodec.list(nodeWorlds.get(node.getKey())));
            rows.add(node.getValue());
            if (!before.contains(node.getKey())) newNodes++;
        }
        for (Map.Entry<String, JsonObject> edge : edges.entrySet()) {
            edge.getValue().add("worlds",
                    ExploreCodec.list(edgeWorlds.get(edge.getKey())));
            rows.add(edge.getValue());
            if (!before.contains(edge.getKey())) newEdges++;
        }
        JsonObject frontier = new JsonObject();
        frontier.addProperty("kind", "FRONTIER");
        frontier.addProperty("round", round);
        frontier.addProperty("nodes", nodes.size());
        frontier.addProperty("edges", edges.size());
        frontier.addProperty("newNodes", newNodes);
        frontier.addProperty("newEdges", newEdges);
        rows.add(frontier);
        RowCodec.writeJsonl(roundDir.resolve(GRAPH), rows);
    }

    /** Writes {@code growth.jsonl}: one EXPOSED_REGION row per occurrence the
     *  closure grows ({@link ClosurePlanner.Plan#exposed}), naming the session
     *  whose replay is re-run and its obligation; returns the row count. */
    static int writeGrowth(Corpus corpus,
                           Map<OccurrenceAddress, String> exposed,
                           Path roundDir) throws IOException {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Map.Entry<OccurrenceAddress, String> grown : exposed.entrySet()) {
            OccurrenceAddress occurrence = grown.getKey();
            SessionReader session = corpus.session(grown.getValue());
            JsonObject row = new JsonObject();
            row.addProperty("kind", "EXPOSED_REGION");
            row.addProperty("regionId", occurrence.regionId());
            row.addProperty("node", occurrence.node().render());
            row.addProperty("occurrence", occurrence.render());
            row.addProperty("sessionId", session.sessionId());
            row.addProperty("obligationId",
                    session.obligations().get(0).obligationId());
            rows.add(row);
        }
        RowCodec.writeJsonl(roundDir.resolve(GROWTH), rows);
        return rows.size();
    }
}
