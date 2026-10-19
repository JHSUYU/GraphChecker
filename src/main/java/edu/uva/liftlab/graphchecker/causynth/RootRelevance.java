package edu.uva.liftlab.graphchecker.causynth;


import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

final class RootRelevance {
    private final Map<String, List<Step>> outgoing = new HashMap<>();
    private final Set<String> stored;
    private final Map<String, List<String>> methodsByRegion;
    private final Map<String, Influence> influences = new HashMap<>();

    RootRelevance(Collection<Map<String, Object>> graph, Set<String> stored,
                  Map<String, List<String>> methodsByRegion) {
        for (Map<String, Object> edge : graph) {
            String from = text(edge.get("fromCell"));
            String to = text(edge.get("toCell"));
            if (from.isEmpty() || to.isEmpty()) continue;
            outgoing.computeIfAbsent(from, ignored -> new ArrayList<>())
                    .add(new Step(text(edge.get("method")), to,
                            "wire_handoff".equals(text(edge.get("kind")))));
        }
        this.stored = stored;
        this.methodsByRegion = methodsByRegion;
    }

    private static final class Step {
        private final String method;
        private final String to;
        private final boolean wire;

        private Step(String method, String to, boolean wire) {
            this.method = method;
            this.to = to;
            this.wire = wire;
        }
    }

    static final class Influence {
        final Set<String> carriers = new LinkedHashSet<>();
        final Set<String> consumers = new LinkedHashSet<>();
        private final Map<String, Set<String>> from = new LinkedHashMap<>();

        Set<String> through(Collection<String> ends) {
            Set<String> cells = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>(ends);
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!cells.add(cell)) continue;
                work.addAll(from.getOrDefault(cell,
                        Collections.<String>emptySet()));
            }
            return cells;
        }
    }

    Influence influence(List<String> regionIds, String cell) {
        String key = String.join(",", regionIds) + "\n" + cell;
        Influence known = influences.get(key);
        if (known != null) return known;
        Set<String> methods = new LinkedHashSet<>();
        for (String regionId : regionIds) {
            methods.addAll(methodsByRegion.getOrDefault(regionId,
                    Collections.<String>emptyList()));
        }
        Influence influence = new Influence();
        influence.from.put(cell, new LinkedHashSet<>());
        Deque<String> work = new ArrayDeque<>();
        work.add(cell);
        while (!work.isEmpty()) {
            String at = work.removeFirst();
            for (Step step : outgoing.getOrDefault(at,
                    Collections.<Step>emptyList())) {
                if (!step.wire && !methods.contains(step.method)) continue;
                boolean fresh = !influence.from.containsKey(step.to);
                influence.from.computeIfAbsent(step.to,
                        ignored -> new LinkedHashSet<>()).add(at);
                if (step.wire) {
                    influence.consumers.add(step.to);
                } else if (stored.contains(step.to)) {
                    influence.carriers.add(step.to);
                } else if (fresh) {
                    work.add(step.to);
                }
            }
        }
        influences.put(key, influence);
        return influence;
    }
}
