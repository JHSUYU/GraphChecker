package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
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

/**
 * G_k, and what the wave's worlds grew it by (DESIGN4 SS3.1-SS3.3, SS3.5).
 *
 * <p>{@code graph.jsonl}, per wave: NODE rows, one per occurrence some
 * ADMITTED session activated (only an admitted replay states a topology),
 * carrying its node, whether it ran instrumented anywhere, and the worlds
 * ({@link ObligationFactory#worldDigest}) it was observed in; EDGE rows,
 * one per (kind, producer endpoint, consumer endpoint) -- WIRE from the
 * attaches' own pairings, STATE from a read to the write of the version it
 * observed -- carrying the worlds that state them.  No THREAD edge: the
 * schedule's START and CLAIM rows carry a context, a site and a count, and
 * no occurrence, so a thread edge between occurrences is not a fact the
 * rows state.  A FRONTIER row compares this wave's node and edge identity
 * sets with the previous wave's.</p>
 *
 * <p>{@code growth.jsonl}, per wave: an EXPOSED_REGION row per (region,
 * occurrence) that an admitted replay's OWN backward closure from the anchor
 * ({@link Corpus#upstreamOf(OccurrenceAddress, List, String)}) holds as an
 * ambient activation of a region the weave does not hold
 * ({@link Corpus#woven}).  The driver weaves those regions, plans them, and
 * re-runs the exposing obligation.  The seed exposes nothing: what it
 * reached ambient is the plan's own admission decision, not a world's
 * growth.</p>
 */
final class WaveGraph {
    static final String GRAPH = "graph.jsonl";
    static final String GROWTH = "growth.jsonl";
    /** A degraded occurrence's region slot: a role, not a region. */
    private static final String ROLE_REGION = "ROLE.";

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

    /** G_k over the corpus's admitted sessions. */
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

    /**
     * Writes {@code graph.jsonl} into the wave directory, its FRONTIER row
     * against the previous wave's file beside it.
     */
    void write(Path waveDir, int wave) throws IOException {
        Set<String> before = new LinkedHashSet<String>();
        if (wave > 0) {
            Path previous = waveDir.resolveSibling(
                    String.format("obligations-%04d", wave - 1))
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
            node.getValue().add("worlds", strings(nodeWorlds.get(node.getKey())));
            rows.add(node.getValue());
            if (!before.contains(node.getKey())) newNodes++;
        }
        for (Map.Entry<String, JsonObject> edge : edges.entrySet()) {
            edge.getValue().add("worlds", strings(edgeWorlds.get(edge.getKey())));
            rows.add(edge.getValue());
            if (!before.contains(edge.getKey())) newEdges++;
        }
        JsonObject frontier = new JsonObject();
        frontier.addProperty("kind", "FRONTIER");
        frontier.addProperty("wave", wave);
        frontier.addProperty("nodes", nodes.size());
        frontier.addProperty("edges", edges.size());
        frontier.addProperty("newNodes", newNodes);
        frontier.addProperty("newEdges", newEdges);
        rows.add(frontier);
        RowCodec.writeJsonl(waveDir.resolve(GRAPH), rows);
    }

    /**
     * Writes {@code growth.jsonl}: the regions the wave's admitted replays
     * exposed, one row per (region, occurrence), first exposing session
     * named.
     *
     * @param anchor the anchor's task, whose focused occurrence and factor
     *               root every session's closure; null plans no closure
     * @return the number of rows written
     */
    static int writeGrowth(Corpus corpus, Task anchor, Path waveDir,
                           List<GapRow> gaps) throws IOException {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        Set<String> exposed = new LinkedHashSet<String>();
        String seed = corpus.seedSessionId();
        for (SessionReader session : anchor == null
                ? new ArrayList<SessionReader>() : corpus.sessions()) {
            if (!session.admitted() || session.sessionId().equals(seed)) {
                continue;
            }
            String obligationId = session.obligations().isEmpty() ? ""
                    : session.obligations().get(0).obligationId();
            for (String id : corpus.upstreamOf(anchor.focused(),
                    anchor.factor(), session.sessionId())) {
                OccurrenceAddress occurrence = corpus.occurrence(id);
                ActivationRow activation = occurrence == null ? null
                        : corpus.activation(session.sessionId(), occurrence);
                if (activation == null || activation.instrumented()
                        || corpus.woven(occurrence.regionId())
                        || !exposed.add(occurrence.regionId() + "|" + id)) {
                    continue;
                }
                if (occurrence.regionId().startsWith(ROLE_REGION)) {
                    gaps.add(GapRow.of(session.sessionId(),
                            GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                            occurrence.render(),
                            "a flipped path reached a region whose scope the "
                                    + "recording lost: " + occurrence.regionId()
                                    + " is a role, not a region of the static "
                                    + "graph, so nothing can weave it"));
                    continue;
                }
                JsonObject row = new JsonObject();
                row.addProperty("kind", "EXPOSED_REGION");
                row.addProperty("regionId", occurrence.regionId());
                row.addProperty("node", occurrence.node().render());
                row.addProperty("occurrence", occurrence.render());
                row.addProperty("sessionId", session.sessionId());
                row.addProperty("obligationId", obligationId);
                rows.add(row);
            }
        }
        RowCodec.writeJsonl(waveDir.resolve(GROWTH), rows);
        return rows.size();
    }

    private static JsonArray strings(Set<String> values) {
        JsonArray array = new JsonArray();
        for (String value : values) array.add(value);
        return array;
    }
}
