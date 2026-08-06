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
 * Builds candidate region skeletons around authoritative execution-context
 * entries.
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

        Map<String, Set<String>> outgoing = new LinkedHashMap<>();
        Set<String> failureMethods = new LinkedHashSet<>();
        Set<String> protocolAnchors = new LinkedHashSet<>();
        Set<String> stateAnchors = new LinkedHashSet<>();
        Set<String> demandedState = failureRelevantState(program.edges);
        for (String method : selected) {
            outgoing.put(method, new LinkedHashSet<>());
        }
        for (Map<String, Object> edge : program.edges) {
            String method = text(edge.get("method"));
            String transfer = text(edge.get("transferKind"));
            String target = text(edge.get("toCell"));
            if (target.contains("#exception:") && selected.contains(method)) {
                failureMethods.add(method);
            }
            if (!text(edge.get("protocolStubMappingId")).isEmpty()) {
                addIfSelected(protocolAnchors, selected, method);
                addIfSelected(protocolAnchors, selected,
                        text(edge.get("protocolServerStub")));
            }
            if (("HEAP_READ".equals(transfer)
                    || "HEAP_WRITE".equals(transfer))
                    && selected.contains(method)
                    && !constructor(method)
                    && demandedState.contains(stateDeclaration(edge,
                    transfer))) {
                stateAnchors.add(method);
            }
            String callee = invocationTarget(edge);
            if (!selected.contains(method) || !selected.contains(callee)
                    || method.equals(callee)
                    || "PROTOCOL_TRANSFER".equals(transfer)) {
                continue;
            }
            outgoing.get(method).add(callee);
        }

        program.regions.clear();
        program.regionEdges.clear();
        List<String> roots = new ArrayList<>(
                program.executionContextAuthorities.keySet());
        Collections.sort(roots);
        for (String root : roots) {
            if (!selected.contains(root) || constructor(root)) {
                continue;
            }
            List<String> methods = forwardClosure(root, outgoing,
                    program.executionContextAuthorities);
            String authority = program.executionContextAuthorities.get(root);
            boolean admitted = addSkeleton(program, root, authority, methods,
                    failureMethods,
                    protocolAnchors, stateAnchors,
                    "STATIC_AUTHORITY_SKELETON");
            if (!admitted) {
                addAuthorityEnvelope(program, root, authority, methods);
            }
        }

        List<String> nestedEndpoints = new ArrayList<>(
                program.nestedContextEndpoints);
        Collections.sort(nestedEndpoints);
        for (String endpoint : nestedEndpoints) {
            if (!selected.contains(endpoint) || constructor(endpoint)) {
                continue;
            }
            addSkeleton(program, endpoint, "NESTED_CALL",
                    forwardClosure(endpoint, outgoing,
                            program.executionContextAuthorities),
                    failureMethods, protocolAnchors, stateAnchors,
                    "STATIC_NESTED_CONTEXT_FRAGMENT");
        }
    }

    private static boolean addSkeleton(
            StaticProgram program, String root, String authority,
            List<String> methods, Set<String> failureMethods,
            Set<String> protocolAnchors, Set<String> stateAnchors,
            String planningMode) {
        List<String> failure = intersections(methods, failureMethods);
        List<String> protocol = intersections(methods, protocolAnchors);
        List<String> state = intersections(methods, stateAnchors);
        List<String> anchors = union(failure, protocol, state);
        if (anchors.isEmpty()) {
            return false;
        }
        String identity = authority + "\n" + root;
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", REGION_SCHEMA_VERSION);
        row.put("kind", SKELETON_KIND);
        row.put("regionId", "REGION."
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8)));
        row.put("rootMethod", root);
        row.put("rootAuthority", authority);
        row.put("anchorMethod", anchors.get(0));
        row.put("anchorMethods", anchors);
        row.put("methods", methods);
        row.put("selection", !failure.isEmpty()
                ? "EXCEPTION_CONTEXT"
                : !protocol.isEmpty()
                ? "PROTOCOL_CONTEXT" : "STATE_CONTEXT");
        row.put("planningMode", planningMode);
        program.regions.add(row);
        return true;
    }

    private static void addAuthorityEnvelope(
            StaticProgram program, String root, String authority,
            List<String> methods) {
        String identity = authority + "\n" + root;
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", REGION_SCHEMA_VERSION);
        row.put("kind", SKELETON_KIND);
        row.put("regionId", "REGION."
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8)));
        row.put("rootMethod", root);
        row.put("rootAuthority", authority);
        row.put("anchorMethod", "");
        row.put("anchorMethods", Collections.emptyList());
        row.put("methods", methods);
        row.put("selection", "AUTHORITY_ENVELOPE");
        row.put("planningMode", "STATIC_AUTHORITY_ENVELOPE");
        program.regions.add(row);
    }

    private static void addIfSelected(Set<String> target,
                                      Set<String> selected, String method) {
        if (selected.contains(method)) {
            target.add(method);
        }
    }

    private static List<String> intersections(List<String> ordered,
                                              Set<String> candidates) {
        List<String> result = new ArrayList<>();
        for (String value : ordered) {
            if (candidates.contains(value)) {
                result.add(value);
            }
        }
        return result;
    }

    private static List<String> forwardClosure(
            String root, Map<String, Set<String>> outgoing,
            Map<String, String> authorities) {
        Set<String> visited = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>();
        work.add(root);
        while (!work.isEmpty()) {
            String method = work.removeFirst();
            if (!visited.add(method)) {
                continue;
            }
            List<String> next = new ArrayList<>(outgoing.getOrDefault(method,
                    Collections.emptySet()));
            Collections.sort(next);
            for (String candidate : next) {
                if (!root.equals(candidate)
                        && authorities.containsKey(candidate)) {
                    continue;
                }
                work.addLast(candidate);
            }
        }
        List<String> result = new ArrayList<>(visited);
        Collections.sort(result);
        return result;
    }

    @SafeVarargs
    private static List<String> union(List<String>... groups) {
        Set<String> unique = new LinkedHashSet<>();
        for (List<String> group : groups) {
            unique.addAll(group);
        }
        return new ArrayList<>(unique);
    }

    private static boolean constructor(String method) {
        return method != null && (method.contains(" <init>(")
                || method.contains(" <clinit>("));
    }

    private static String invocationTarget(Map<String, Object> edge) {
        if ("DYNAMIC_DISPATCH".equals(text(edge.get("transferKind")))
                && "dispatch_activation".equals(text(edge.get("kind")))) {
            String activation = text(edge.get("toCell"));
            if (activation.endsWith(".activation")) {
                return activation.substring(0,
                        activation.length() - ".activation".length());
            }
        }
        return text(edge.get("invoke"));
    }

    /**
     * Finds declared state read by the failure slice, then admits only roots
     * that access that state.  The old rule treated every selected heap access
     * as a region anchor, which turned broad call-graph scaffolding into
     * hundreds of unrelated region candidates.
     */
    private static Set<String> failureRelevantState(
            Collection<Map<String, Object>> edges) {
        Map<String, List<Map<String, Object>>> incoming =
                new LinkedHashMap<>();
        Deque<String> work = new ArrayDeque<>();
        for (Map<String, Object> edge : edges) {
            String target = text(edge.get("toCell"));
            if (!target.isEmpty()) {
                incoming.computeIfAbsent(target,
                        ignored -> new ArrayList<>()).add(edge);
            }
            if (target.contains("#exception:")) {
                work.addLast(target);
            }
        }

        Set<String> visited = new LinkedHashSet<>();
        Set<String> demanded = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            String cell = work.removeFirst();
            if (!visited.add(cell)) continue;
            for (Map<String, Object> edge : incoming.getOrDefault(cell,
                    Collections.emptyList())) {
                String transfer = text(edge.get("transferKind"));
                String source = text(edge.get("fromCell"));
                if ("HEAP_READ".equals(transfer)
                        && declaredField(source)) {
                    demanded.add(source);
                }
                if (!source.isEmpty()) work.addLast(source);
            }
        }
        return demanded;
    }

    private static String stateDeclaration(Map<String, Object> edge,
                                           String transfer) {
        String cell = text(edge.get("HEAP_READ".equals(transfer)
                ? "fromCell" : "toCell"));
        return declaredField(cell) ? cell : "";
    }

    private static boolean declaredField(String cell) {
        return cell.startsWith("<") && cell.endsWith(">")
                && cell.contains(":") && !cell.contains("(");
    }

    static boolean validRootAuthority(String authority) {
        if (authority == null) {
            return false;
        }
        switch (authority) {
            case "THREAD_ENTRY":
            case "TASK_ENTRY":
            case "MAIN_ENTRY":
            case "RPC_HANDLER":
                return true;
            default:
                return false;
            }
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }
}
