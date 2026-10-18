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

/**
 * THE STORE EDGES A REPLAY RAN PAST THE CHAIN (PIPELINE §7.8, SYMBOL-SCOPE
 * §6.4): the chain is a finite set of (znode, field), and it grows only by a
 * field of it.  A replay's write of a chain path's version by an occurrence
 * off the chain -- a STORE write, or a VIEW write, a node's decode -- is one
 * {@value ZkChain#EDGE} growth row of the round where a chain occurrence of
 * the same session read that version (a STORE read or a chain decode of
 * it; a VIEW read of that node's view) and the occurrence's own leaves of
 * the path (its content ports) lie under a key the chain holds of it: the
 * row's {@code pointers} are those keys.  Not an edge: any other decode or
 * write of a chain path (another node's view, a version no chain occurrence
 * consumed, a document whose chain fields it never touched), a chain path
 * the chain holds no field of, a read of a path off the chain (a poll), and
 * work under no region, which no task can hold (solr-18413 SGF7: every such
 * one grown, round 2's growth was 1099 rows over 541 occurrences, and its
 * GROW's argument list overflowed).  Once per (transport, path, version,
 * occurrence); named by the first admitted focused replay that shows it,
 * which GROW re-runs, else by none ({@code sessionId} ""): the chain grows
 * all the same, and no replay is re-run.
 */
final class ZkEdges {
    private ZkEdges() {
    }

    /** The round's growth rows, in corpus and row order. */
    static List<JsonObject> of(Corpus corpus, ZkChain chain)
            throws IOException {
        Map<String, JsonObject> edges = new LinkedHashMap<String, JsonObject>();
        Map<String, Set<String>> keys = chain.pointers();
        if (keys.isEmpty()) return new ArrayList<JsonObject>();
        // Each session's writes past the chain found on a core of its own
        // (Parallel#map), taken in the corpus's order.
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

    /** One store write a replay ran past the chain, and the chain's
     *  fields it wrote. */
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

    /** One session's writes past the chain, in its rows' order. */
    private static List<OffChain> offChain(SessionReader session,
                                           ZkChain chain,
                                           Map<String, Set<String>> keys) {
        List<OffChain> found = new ArrayList<OffChain>();
        boolean exposing = !session.seed() && session.admitted();
        Set<String> consumed = consumed(session, chain);
        Map<String, Set<String>> leaves = null;
        for (WriteRow write : session.writes()) {
            // An INITIAL's endpoint observed the location; it wrote
            // nothing.
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

    /** The versions a session's chain occurrences consumed ({@link
     *  #version}): each STORE or VIEW read of one, and each STORE version a
     *  chain decode decoded. */
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

    /** One version of a STORE or VIEW location (a view by its node). */
    private static String version(LocationId location, long version) {
        return location.kind() + "\n" + location.owner() + "\n"
                + location.slot() + "\n" + version;
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
