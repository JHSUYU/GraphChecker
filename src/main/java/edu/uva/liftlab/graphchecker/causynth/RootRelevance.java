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

/**
 * Where a root an occurrence read goes inside it (R1-ROOTS item 3,
 * SYMBOL-SCOPE §4.4): its influence, by which {@link
 * RuntimeSelectedRegionFinalizer} admits a root-reading occurrence.
 *
 * <p>The influence is the forward reach of the read's dependency cell over
 * the candidate graph, through the methods the occurrence performed (its
 * region's and those of the regions folded into it), along value, guard and
 * exception edges alike.  It ends at a stored location -- a cell some
 * WRITE_SITE names: the carrier a store writes, or would write on the arm
 * the root decides, which the recording may never have taken -- and at a
 * wire producer, whose {@code wire_handoff} names the consumer cell the
 * value is handed to on another node.  The candidate graph holds only edges
 * the backward slice put there, so every forward path already leads toward
 * the failure, and the reach stays small.  A fault decides whether a message
 * exists instead ({@link RecordedMessages#doorsOf}).</p>
 */
final class RootRelevance {
    /** Candidate edges by the cell they leave. */
    private final Map<String, List<Step>> outgoing = new HashMap<>();
    /** Every location a WRITE_SITE names. */
    private final Set<String> stored;
    /** Each region's methods: an occurrence performs those of its regions. */
    private final Map<String, List<String>> methodsByRegion;
    private final Map<String, Influence> influences = new HashMap<>();

    /**
     * @param graph           the candidate graph's rows
     * @param stored          every location a WRITE_SITE of the scope map
     *                        names ({@code StaticScopeMap#writeSitesByCell})
     * @param methodsByRegion each region skeleton's methods
     */
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

    /** One candidate edge out of a cell. */
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

    /** Where one root read's value and decisions go inside its occurrence. */
    static final class Influence {
        /** The stored locations it reaches. */
        final Set<String> carriers = new LinkedHashSet<>();
        /** The wire consumer cells its value is handed to. */
        final Set<String> consumers = new LinkedHashSet<>();
        /** Each reached cell and end, with the cells it was reached from. */
        private final Map<String, Set<String>> from = new LinkedHashMap<>();

        /**
         * The cells on the reach's paths into {@code ends} (carriers or
         * consumer cells it reached), the root's cell and the ends included:
         * the way the root enters what the failure demands.
         */
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

    /**
     * The influence of the value {@code cell} holds in an occurrence that
     * performed {@code regionIds}; one computation per (regions, cell).
     */
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
