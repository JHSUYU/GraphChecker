package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Parallel;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.UnplannedInput;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/** G_k and its growth (PIPELINE §7.1, §7.8). {@code graph.jsonl.gz}: NODE
 *  per activated occurrence, EDGE per WIRE pairing or STATE join, with worlds
 *  ({@link ObligationFactory#worldDigest}), plus a FRONTIER diff; no THREAD
 *  edge (schedule rows carry no occurrence). {@code growth.jsonl}: the
 *  occurrences the closure demands and no session captured ({@link
 *  ClosurePlanner.Plan#exposed}). */
final class WaveGraph {
    /** gzip: SGF8-adhoc-05 round 4's, 368 MB as text, is 10 MB. */
    static final String GRAPH = "graph.jsonl.gz";
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

    /** Every admitted session's nodes and edges, each session's found and
     *  its edges' ids digested on a core of its own ({@link Parallel#map}),
     *  taken in the sessions' order. */
    static WaveGraph of(Corpus corpus) throws IOException {
        WaveGraph graph = new WaveGraph();
        List<SessionReader> admitted = new ArrayList<SessionReader>();
        for (SessionReader session : corpus.sessions()) {
            if (session.admitted()) admitted.add(session);
        }
        for (Ran ran : Parallel.map(admitted, session -> new Ran(corpus,
                session))) {
            for (ActivationRow activation : ran.session.activations()) {
                graph.node(activation.occurrence(), activation.instrumented(),
                        ran.world);
            }
            for (Edge edge : ran.edges) {
                graph.edge(edge, ran.world);
            }
        }
        return graph;
    }

    /** What one admitted session states of the graph: its world, and its
     *  WIRE pairings, then its STATE joins, in its rows' order. */
    private static final class Ran {
        final SessionReader session;
        final String world;
        final List<Edge> edges = new ArrayList<Edge>();

        Ran(Corpus corpus, SessionReader session) {
            this.session = session;
            this.world = ObligationFactory.worldDigest(
                    corpus.world(session.sessionId()));
            for (AttachRow attach : session.attaches()) {
                if (attach.producer() == null) continue;
                edges.add(new Edge(InteractionKind.WIRE, attach.producer(),
                        attach.endpoint()));
            }
            for (ReadRow read : session.reads()) {
                WriteRow write = corpus.writeOf(read.sessionId(),
                        read.location(), read.observedVersion());
                if (write == null) continue;
                edges.add(new Edge(InteractionKind.STATE, write.endpoint(),
                        read.endpoint()));
            }
        }
    }

    /** One pairing or join, with its interaction's id. */
    private static final class Edge {
        final InteractionKind kind;
        final Endpoint producer;
        final Endpoint consumer;
        final String id;

        Edge(InteractionKind kind, Endpoint producer, Endpoint consumer) {
            this.kind = kind;
            this.producer = producer;
            this.consumer = consumer;
            this.id = Interaction.of(kind, producer, consumer).id();
        }
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

    private void edge(Edge edge, String world) {
        JsonObject row = edges.get(edge.id);
        if (row == null) {
            row = new JsonObject();
            row.addProperty("kind", "EDGE");
            row.addProperty("edgeId", edge.id);
            row.addProperty("edge", edge.kind.name());
            row.addProperty("producer", edge.producer.render());
            row.addProperty("producerOccurrenceId",
                    edge.producer.occurrence().id());
            row.addProperty("consumer", edge.consumer.render());
            row.addProperty("consumerOccurrenceId",
                    edge.consumer.occurrence().id());
            edges.put(edge.id, row);
            edgeWorlds.put(edge.id, new TreeSet<String>());
        }
        edgeWorlds.get(edge.id).add(world);
    }

    /** Writes {@code graph.jsonl.gz} with its FRONTIER against the previous
     *  round's. */
    void write(Path roundDir, int round) throws IOException {
        Set<String> before = new LinkedHashSet<String>();
        if (round > 0) {
            Path previous = roundDir.resolveSibling(
                    String.format("obligations-%04d", round - 1))
                    .resolve(GRAPH);
            // Its ids alone, each line parsed on a core (RowCodec#readEach).
            RowCodec.readEach(previous, row -> {
                List<String> ids = new ArrayList<String>(1);
                if (row.has("occurrenceId")) {
                    ids.add(row.get("occurrenceId").getAsString());
                }
                if (row.has("edgeId")) {
                    ids.add(row.get("edgeId").getAsString());
                }
                return ids;
            }, before::addAll);
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
     *  closure grows ({@link ClosurePlanner.Plan#exposed}), one
     *  DOORS_ONLY_UNPAUSED row per doors-only occurrence a value demand
     *  reached ({@link ClosurePlanner.Plan#unpaused}: GROW drops its mark),
     *  one UNPLANNED_INPUT row per marker invocation a flipped world added
     *  ({@link ClosurePlanner#unplanned}), each naming the session whose
     *  replay is re-run, if any, and its obligation, and the ZK_EDGE rows of
     *  the store edges its replays ran past the ZooKeeper chain ({@link
     *  ZkEdges}); returns the row count. */
    static int writeGrowth(Corpus corpus,
                           Map<OccurrenceAddress, String> exposed,
                           Map<OccurrenceAddress, String> unpaused,
                           Map<UnplannedInput, String> inputs,
                           List<JsonObject> zkEdges,
                           Path roundDir) throws IOException {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Map.Entry<OccurrenceAddress, String> grown : exposed.entrySet()) {
            rows.add(growthRow("EXPOSED_REGION", corpus, grown.getKey(),
                    grown.getValue()));
        }
        for (Map.Entry<OccurrenceAddress, String> door : unpaused.entrySet()) {
            rows.add(growthRow(DOORS_ONLY_UNPAUSED, corpus, door.getKey(),
                    door.getValue()));
        }
        for (Map.Entry<UnplannedInput, String> grown : inputs.entrySet()) {
            UnplannedInput input = grown.getKey();
            JsonObject row = exposing(corpus, grown.getValue());
            row.addProperty("kind", "UNPLANNED_INPUT");
            row.addProperty("taskId", input.taskId());
            row.addProperty("symbol", input.symbol());
            row.addProperty("k", input.k());
            rows.add(row);
        }
        rows.addAll(zkEdges);
        RowCodec.writeJsonl(roundDir.resolve(GROWTH), rows);
        return rows.size();
    }

    /** A growth row's kind for a doors-only occurrence a value demand
     *  reached. */
    static final String DOORS_ONLY_UNPAUSED = "DOORS_ONLY_UNPAUSED";

    /** One growth row of an occurrence; a session "" names no replay to
     *  re-run. */
    private static JsonObject growthRow(String kind, Corpus corpus,
                                        OccurrenceAddress occurrence,
                                        String sessionId) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", kind);
        row.addProperty("regionId", occurrence.regionId());
        row.addProperty("node", occurrence.node().render());
        row.addProperty("occurrence", occurrence.render());
        row.addProperty("sessionId", sessionId);
        row.addProperty("obligationId", sessionId.isEmpty() ? ""
                : corpus.session(sessionId).obligations().get(0)
                .obligationId());
        return row;
    }

    /** A growth row's exposing session and its obligation. */
    private static JsonObject exposing(Corpus corpus, String sessionId) {
        SessionReader session = corpus.session(sessionId);
        JsonObject row = new JsonObject();
        row.addProperty("sessionId", session.sessionId());
        row.addProperty("obligationId",
                session.obligations().get(0).obligationId());
        return row;
    }
}
