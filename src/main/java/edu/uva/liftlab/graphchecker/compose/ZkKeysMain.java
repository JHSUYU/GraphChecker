package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class ZkKeysMain {
    private ZkKeysMain() {
    }

    public static void main(String[] argv) throws IOException {
        LongOptions options = LongOptions.parse(argv);
        Path chainFile = options.path("zk-chain");
        ZkChain chain = ZkChain.read(chainFile);
        if (chain.empty()) {
            System.out.println("zk keys: no ZooKeeper chain, nothing keyed");
            return;
        }
        Path sessions = options.path("sessions");
        Corpus corpus = Corpus.read(sessions.getParent(),
                options.path("root-domains"), null, null);
        OccurrenceAddress anchor = ComposeMain.anchorOf(
                options.value("anchor", ""), corpus);
        Composer.Composition composition = Composer.compose(corpus, anchor,
                1, StaticScopeMap.read(options.path("static-scope-map")));
        if (composition.disjuncts().isEmpty()) {
            System.out.println("zk keys: the seed composes no path to the"
                    + " anchor, PLAN's keys kept");
            return;
        }
        Set<String> ports = ports(corpus, composition.body());
        for (SessionReader reader : corpus.sessions()) {
            ports.addAll(handedOn(corpus, reader.sessionId(), anchor));
        }
        Path planFile = options.path("plan");
        List<JsonObject> plan = ArtifactIO.readJsonl(planFile);
        ZkChain rekeyed = chain.rekeyed(keys(chain, plan, pointers(ports)));
        int rows = 0;
        for (JsonObject task : plan) {
            if (!task.has(ZkChain.CONTENT_KEYS)) continue;
            task.add(ZkChain.CONTENT_KEYS, rekeyed.contentKeys(
                    optionalString(task, "occurrenceId")));
            rows++;
        }
        rekeyed.write(chainFile);
        ArtifactIO.replaceJsonl(planFile, plan);
        System.out.println("zk keys: " + ports.size() + " content leaf"
                + " port(s) the anchor's question rests on ("
                + composition.disjuncts().size() + " path(s) composed), "
                + rows + " task row(s) rekeyed");
    }

    public static Set<String> ports(Corpus corpus, String body) {
        Set<String> named = new HashSet<String>(SmtNames.names(body));
        Set<String> ports = new TreeSet<String>();
        for (SessionReader reader : corpus.sessions()) {
            for (AttachRow attach : reader.attaches()) {
                String port = attach.endpoint().site();
                if (ContentPort.is(port) && named.contains(
                        SmtNames.legalSymbols(attach.symbol()))) {
                    ports.add(port);
                }
            }
        }
        return ports;
    }

    static Set<String> handedOn(Corpus corpus, String session,
                                OccurrenceAddress anchor) {
        Set<String> ports = new TreeSet<String>();
        Set<String> seen = new HashSet<String>();
        Deque<OccurrenceAddress> work = new ArrayDeque<OccurrenceAddress>();
        work.add(anchor);
        seen.add(anchor.id());
        SmtLowering lowering = corpus.lowering(session);
        while (!work.isEmpty()) {
            OccurrenceAddress occurrence = work.removeFirst();
            for (DecisionRow decision
                    : corpus.decisionsOf(session, occurrence)) {
                ports.addAll(leafPorts(corpus, session, lowering,
                        decision.term()));
            }
            for (AttachRow attach : corpus.attachesOn(session, occurrence)) {
                if (attach.producer() == null) continue;
                OccurrenceAddress from = attach.producer().occurrence();
                if (seen.add(from.id())) work.add(from);
            }
            for (ReadRow read : corpus.readsOn(session, occurrence)) {
                WriteRow write = corpus.writeOf(session, read.location(),
                        read.observedVersion());
                if (write == null) continue;
                OccurrenceAddress from = write.endpoint().occurrence();
                if (seen.add(from.id())) work.add(from);
            }
        }
        return ports;
    }

    static Set<String> leafPorts(Corpus corpus, String session,
                                 SmtLowering lowering, String term) {
        Set<String> ports = new TreeSet<String>();
        if (term == null || term.isEmpty() || lowering == null) return ports;
        String lowered = lowering.statedTerm(term, "zk-keys:" + session);
        String text = lowered.isEmpty() ? term : lowered;
        Set<String> symbols = new LinkedHashSet<String>(
                lowering.reachedSymbols(Collections.singletonList(text)));
        SmtNames.symbols(text, symbols);
        for (String symbol : symbols) {
            if (corpus.symbolKind(session, symbol)
                    != Corpus.SymbolKind.HANDOFF) {
                continue;
            }
            AttachRow attach = corpus.attach(session, symbol);
            if (attach != null && ContentPort.is(attach.endpoint().site())) {
                ports.add(attach.endpoint().site());
            }
        }
        return ports;
    }

    static Map<String, Set<String>> pointers(Set<String> ports) {
        Map<String, Set<String>> pointers =
                new LinkedHashMap<String, Set<String>>();
        for (String port : ports) {
            ContentPort.Parsed leaf = ContentPort.parse(port);
            pointers.computeIfAbsent(leaf.location,
                    slot -> new TreeSet<String>())
                    .add(ContentPort.pointer(leaf.pointer));
        }
        return pointers;
    }

    static List<JsonObject> keys(ZkChain chain, List<JsonObject> plan,
                                 Map<String, Set<String>> pointers) {
        Map<String, String> locations = new HashMap<String, String>();
        Map<String, Set<String>> slotsOf =
                new LinkedHashMap<String, Set<String>>();
        for (JsonObject row : chain.rows()) {
            String kind = optionalString(row, "kind");
            String slot = optionalString(row, "slot");
            if (ZkChain.PATH.equals(kind) || ZkChain.KEYS.equals(kind)) {
                locations.putIfAbsent(slot, optionalString(row, "location"));
            }
            if (ZkChain.KEYS.equals(kind)) {
                slotsOf.computeIfAbsent(optionalString(row, "occurrenceId"),
                        occurrence -> new LinkedHashSet<String>()).add(slot);
            }
        }
        for (JsonObject task : plan) {
            if (task.has(ZkChain.CONTENT_KEYS)) {
                slotsOf.computeIfAbsent(optionalString(task, "occurrenceId"),
                        occurrence -> new LinkedHashSet<String>());
            }
        }
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Map.Entry<String, Set<String>> keyed : slotsOf.entrySet()) {
            Set<String> slots = new LinkedHashSet<String>(keyed.getValue());
            slots.addAll(pointers.keySet());
            for (String slot : slots) {
                JsonObject row = new JsonObject();
                row.addProperty("schemaVersion", 1);
                row.addProperty("kind", ZkChain.KEYS);
                row.addProperty("occurrenceId", keyed.getKey());
                String location = locations.get(slot);
                row.addProperty("location", location == null
                        || location.isEmpty() ? slot : location);
                row.addProperty("slot", slot);
                JsonArray held = new JsonArray();
                Set<String> named = pointers.get(slot);
                if (named != null) {
                    for (String pointer : named) held.add(pointer);
                }
                row.add("pointers", held);
                rows.add(row);
            }
        }
        return rows;
    }
}
