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
import edu.uva.liftlab.graphchecker.contract.Parallel;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.contract.ZkChain;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class ZkEdges {
    private ZkEdges() {
    }

    static List<JsonObject> of(Corpus corpus, ZkChain chain)
            throws IOException {
        Map<String, JsonObject> edges = new LinkedHashMap<String, JsonObject>();
        Map<String, Set<String>> keys = chain.pointers();
        if (keys.isEmpty()) return new ArrayList<JsonObject>();
        for (List<OffChain> found : Parallel.map(corpus.sessions(),
                session -> offChain(session, chain, keys))) {
            for (OffChain write : found) {
                edge(edges, write.transport, write.write.location(),
                        write.write.version(),
                        write.write.endpoint().occurrence(), write.session,
                        write.exposing, write.fields);
            }
        }
        return new ArrayList<JsonObject>(edges.values());
    }

    private static final class OffChain {
        final SessionReader session;
        final boolean exposing;
        final String transport;
        final WriteRow write;
        final Set<String> fields;

        OffChain(SessionReader session, boolean exposing, String transport,
                 WriteRow write, Set<String> fields) {
            this.session = session;
            this.exposing = exposing;
            this.transport = transport;
            this.write = write;
            this.fields = fields;
        }
    }

    private static List<OffChain> offChain(SessionReader session,
                                           ZkChain chain,
                                           Map<String, Set<String>> keys) {
        List<OffChain> found = new ArrayList<OffChain>();
        boolean exposing = !session.seed() && session.admitted();
        Set<String> consumed = consumed(session, chain);
        Map<String, Set<String>> leaves = null;
        for (WriteRow write : session.writes()) {
            LocationId location = write.location();
            String transport = transport(location);
            OccurrenceAddress at = write.endpoint().occurrence();
            Set<String> held = transport == null ? null
                    : keys.get(location.slot());
            if (held == null || write.initial() || at.role()
                    || chain.holds(at.render())
                    || !chain.holdsPath(transport, location.slot())
                    || !consumed.contains(version(location,
                    write.version()))) {
                continue;
            }
            if (leaves == null) leaves = leaves(session);
            Set<String> fields = new LinkedHashSet<String>();
            for (String leaf : leaves.getOrDefault(at.render() + "\n"
                    + location.slot(), Collections.<String>emptySet())) {
                for (String key : held) {
                    if (ContentPort.covers(Collections.singleton(key),
                            leaf)) {
                        fields.add(key);
                    }
                }
            }
            if (!fields.isEmpty()) {
                found.add(new OffChain(session, exposing, transport, write,
                        fields));
            }
        }
        return found;
    }

    private static Set<String> consumed(SessionReader session, ZkChain chain) {
        Set<String> consumed = new HashSet<String>();
        for (ReadRow read : session.reads()) {
            if (transport(read.location()) != null && chain.holds(
                    read.endpoint().occurrence().render())) {
                consumed.add(version(read.location(),
                        read.observedVersion()));
            }
        }
        for (WriteRow write : session.writes()) {
            LocationId location = write.location();
            if (location.kind() == LocationKind.VIEW && chain.holds(
                    write.endpoint().occurrence().render())) {
                consumed.add(LocationKind.STORE + "\n"
                        + transport(location) + "\n" + location.slot()
                        + "\n" + write.version());
            }
        }
        return consumed;
    }

    private static String version(LocationId location, long version) {
        return location.kind() + "\n" + location.owner() + "\n"
                + location.slot() + "\n" + version;
    }

    private static String transport(LocationId location) {
        if (location.kind() == LocationKind.STORE) return location.owner();
        if (location.kind() != LocationKind.VIEW) return null;
        int at = location.owner().indexOf('@');
        return at < 0 ? location.owner() : location.owner().substring(0, at);
    }

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
                    .add(ContentPort.pointer(leaf.pointer));
        }
        return leaves;
    }

    private static void edge(Map<String, JsonObject> edges, String transport,
                             LocationId location, long version,
                             OccurrenceAddress occurrence,
                             SessionReader session, boolean exposing,
                             Set<String> fields) {
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
        for (String field : fields) pointers.add(field);
        row.add("pointers", pointers);
        edges.put(key, row);
    }
}
