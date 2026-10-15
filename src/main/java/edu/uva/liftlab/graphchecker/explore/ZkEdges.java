package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.contract.ZkChain;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * THE STORE EDGES A REPLAY RAN PAST THE CHAIN (PIPELINE §7.8, SYMBOL-SCOPE
 * §6.4): a run's row that names a chain path's version written or decoded
 * by an occurrence off the chain -- a STORE write, or a VIEW write, a
 * node's decode -- or a path off the chain that a chain occurrence read
 * (a STORE or VIEW read) is one {@value ZkChain#EDGE} growth row of the
 * round, once per (transport, path, version, occurrence): GROW adds the
 * path and the occurrence to the next generation's chain, the occurrence
 * planned (or its doors-only mark dropped) and the replay that showed the
 * edge run again.  Named by the first admitted focused replay that shows
 * it, which GROW re-runs; by none ({@code sessionId} "") where only the
 * seed or unadmitted replays show it: the chain grows all the same, and no
 * replay is re-run.  Each row states the leaf pointers its replay named at
 * the occurrence for that path ({@code pointers}: the content ports of its
 * attaches and exports there), which key a path new to the chain field by
 * field ({@link ZkChain#grown}).
 */
final class ZkEdges {
    private ZkEdges() {
    }

    /** The round's growth rows, in corpus and row order. */
    static List<JsonObject> of(Corpus corpus, ZkChain chain) {
        Map<String, JsonObject> edges = new LinkedHashMap<String, JsonObject>();
        if (chain.empty()) return new ArrayList<JsonObject>();
        for (SessionReader session : corpus.sessions()) {
            boolean exposing = !session.seed() && session.admitted();
            Map<String, Set<String>> leaves = null;
            for (WriteRow write : session.writes()) {
                // An INITIAL's endpoint observed the location; it wrote
                // nothing.
                if (write.initial()) continue;
                String transport = transport(write.location());
                OccurrenceAddress at = write.endpoint().occurrence();
                if (transport != null && chain.holdsPath(transport,
                        write.location().slot())
                        && !chain.holds(at.render())) {
                    if (leaves == null) leaves = leaves(session);
                    edge(edges, transport, write.location(), write.version(),
                            at, session, exposing, leaves);
                }
            }
            for (ReadRow read : session.reads()) {
                String transport = transport(read.location());
                OccurrenceAddress at = read.endpoint().occurrence();
                if (transport != null && chain.holds(at.render())
                        && !chain.holdsPath(transport,
                        read.location().slot())) {
                    if (leaves == null) leaves = leaves(session);
                    edge(edges, transport, read.location(),
                            read.observedVersion(), at, session, exposing,
                            leaves);
                }
            }
        }
        return new ArrayList<JsonObject>(edges.values());
    }

    /** A store location's transport: a STORE's owner, a VIEW's before its
     *  node ({@code transport@node}); null for any other kind. */
    private static String transport(LocationId location) {
        if (location.kind() == LocationKind.STORE) return location.owner();
        if (location.kind() != LocationKind.VIEW) return null;
        int at = location.owner().indexOf('@');
        return at < 0 ? location.owner() : location.owner().substring(0, at);
    }

    /** occurrence + "\n" + slot -> the leaf pointers a session's content
     *  ports name there, as a plan's keys spell them. */
    private static Map<String, Set<String>> leaves(SessionReader session) {
        Map<String, Set<String>> leaves =
                new LinkedHashMap<String, Set<String>>();
        List<Endpoint> ports = new ArrayList<Endpoint>();
        for (AttachRow attach : session.attaches()) {
            ports.add(attach.endpoint());
        }
        for (ExportRow export : session.exports()) {
            ports.add(export.endpoint());
        }
        for (Endpoint port : ports) {
            ContentPort.Parsed leaf = ContentPort.parse(port.site());
            if (leaf == null) continue;
            leaves.computeIfAbsent(port.occurrence().render() + "\n"
                            + leaf.location,
                    key -> new LinkedHashSet<String>())
                    .add(ContentPort.spelled(leaf.pointer));
        }
        return leaves;
    }

    private static void edge(Map<String, JsonObject> edges, String transport,
                             LocationId location, long version,
                             OccurrenceAddress occurrence,
                             SessionReader session, boolean exposing,
                             Map<String, Set<String>> leaves) {
        String key = transport + "\n" + location.slot() + "\n" + version
                + "\n" + occurrence.render();
        JsonObject held = edges.get(key);
        if (held != null && (!exposing
                || !held.get("sessionId").getAsString().isEmpty())) {
            return;
        }
        JsonObject row = new JsonObject();
        row.addProperty("kind", ZkChain.EDGE);
        row.addProperty("transport", transport);
        row.addProperty("location", location.slot());
        row.addProperty("version", version);
        row.addProperty("occurrence", occurrence.render());
        row.addProperty("sessionId", exposing ? session.sessionId() : "");
        row.addProperty("obligationId", exposing
                ? session.obligations().get(0).obligationId() : "");
        JsonArray pointers = new JsonArray();
        Set<String> named = leaves.get(occurrence.render() + "\n"
                + location.slot());
        if (named != null) {
            for (String pointer : named) pointers.add(pointer);
        }
        row.add("pointers", pointers);
        edges.put(key, row);
    }
}
