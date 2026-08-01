package edu.uva.liftlab.graphchecker.causynth;

import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

/**
 * Partitions the cheap static method graph into candidate region skeletons.
 *
 * <p>This phase deliberately knows nothing about REGION.IN, REGION.OUT or
 * field paths.  Those facts require a concrete activation and are produced
 * only after the REGION_STATE pass.</p>
 */
final class SymbolicRegionPlanner {
    static final int REGION_SCHEMA_VERSION = 3;
    static final String SKELETON_KIND = "REGION_SKELETON";

    private SymbolicRegionPlanner() {
    }

    static void planSelectedSkeleton(
            StaticProgram program, Collection<String> selectedMethods) {
        Set<String> selected = new LinkedHashSet<>();
        if (selectedMethods != null) {
            selected.addAll(selectedMethods);
        }
        selected.remove("");

        Map<String, Set<String>> neighbors = new LinkedHashMap<>();
        Map<String, Set<String>> parents = new LinkedHashMap<>();
        Set<String> failureMethods = new LinkedHashSet<>();
        Set<String> protocolAnchors = new LinkedHashSet<>();
        for (String method : selected) {
            neighbors.put(method, new LinkedHashSet<>());
            parents.put(method, new LinkedHashSet<>());
        }
        for (Map<String, Object> edge : program.edges) {
            String method = text(edge.get("method"));
            String invoke = text(edge.get("invoke"));
            String transfer = text(edge.get("transferKind"));
            String target = text(edge.get("toCell"));
            if (target.contains("#exception:") && selected.contains(method)) {
                failureMethods.add(method);
            }
            if (!text(edge.get("protocolStubMappingId")).isEmpty()) {
                addIfSelected(protocolAnchors, selected, method);
                addIfSelected(protocolAnchors, selected,
                        text(edge.get("protocolClientStub")));
                addIfSelected(protocolAnchors, selected,
                        text(edge.get("protocolServerStub")));
            }
            if (!selected.contains(method) || !selected.contains(invoke)
                    || method.equals(invoke) || boundary(transfer)) {
                continue;
            }
            neighbors.get(method).add(invoke);
            neighbors.get(invoke).add(method);
            parents.get(invoke).add(method);
        }

        List<List<String>> components = components(selected, neighbors);
        program.regions.clear();
        program.regionEdges.clear();
        for (List<String> methods : components) {
            List<String> anchors = intersections(methods, failureMethods,
                    protocolAnchors);
            if (anchors.isEmpty()) {
                anchors.add(methods.get(methods.size() - 1));
            }
            for (String anchor : anchors) {
                String root = root(methods, parents, anchor);
                String identity = String.join("\n", methods) + "\n" + root
                        + "\n" + anchor;
                Map<String, Object> row = new LinkedHashMap<>();
                row.put("schemaVersion", REGION_SCHEMA_VERSION);
                row.put("kind", SKELETON_KIND);
                row.put("regionId", "REGION."
                        + UUID.nameUUIDFromBytes(identity.getBytes(
                        StandardCharsets.UTF_8)));
                row.put("rootMethod", root);
                row.put("anchorMethod", anchor);
                row.put("methods", methods);
                row.put("selection", failureMethods.contains(anchor)
                        ? "EXCEPTION_COMPONENT"
                        : protocolAnchors.contains(anchor)
                        ? "PROTOCOL_COMPONENT" : "CANDIDATE_COMPONENT");
                row.put("planningMode", "STATIC_SKELETON_ONLY");
                program.regions.add(row);
            }
        }
    }

    private static void addIfSelected(Set<String> target,
                                      Set<String> selected, String method) {
        if (selected.contains(method)) {
            target.add(method);
        }
    }

    @SafeVarargs
    private static List<String> intersections(List<String> ordered,
                                              Set<String>... candidates) {
        List<String> result = new ArrayList<>();
        for (String value : ordered) {
            for (Set<String> candidate : candidates) {
                if (candidate.contains(value)) {
                    result.add(value);
                    break;
                }
            }
        }
        return result;
    }

    private static boolean boundary(String transfer) {
        return "PROTOCOL_TRANSFER".equals(transfer)
                || "DYNAMIC_DISPATCH".equals(transfer);
    }

    private static List<List<String>> components(
            Set<String> selected, Map<String, Set<String>> neighbors) {
        List<String> ordered = new ArrayList<>(selected);
        Collections.sort(ordered);
        Set<String> visited = new LinkedHashSet<>();
        List<List<String>> result = new ArrayList<>();
        for (String seed : ordered) {
            if (!visited.add(seed)) {
                continue;
            }
            List<String> component = new ArrayList<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(seed);
            while (!work.isEmpty()) {
                String method = work.removeFirst();
                component.add(method);
                List<String> next = new ArrayList<>(neighbors.get(method));
                Collections.sort(next);
                for (String candidate : next) {
                    if (visited.add(candidate)) {
                        work.addLast(candidate);
                    }
                }
            }
            Collections.sort(component);
            result.add(component);
        }
        return result;
    }

    private static String root(List<String> methods,
                               Map<String, Set<String>> parents,
                               String fallback) {
        for (String method : methods) {
            Set<String> incoming = new LinkedHashSet<>(parents.get(method));
            incoming.retainAll(methods);
            if (incoming.isEmpty()) {
                return method;
            }
        }
        return fallback;
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }
}
