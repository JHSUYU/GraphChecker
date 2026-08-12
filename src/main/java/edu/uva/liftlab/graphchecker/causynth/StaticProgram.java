package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Canonical in-memory artifact set for one static analysis run. */
final class StaticProgram {
    final List<Map<String, Object>> edges = new ArrayList<>();
    final List<String> traceMethods = new ArrayList<>();
    /**
     * Methods that are allowed to own a REGION activation.  The value is a
     * project-independent authority such as THREAD_ENTRY, TASK_ENTRY,
     * MAIN_ENTRY, RPC_HANDLER, or a configured WORKLOAD_ENTRY. Constructors
     * and ordinary helpers never appear here.
     */
    final Map<String, String> executionContextAuthorities =
            new LinkedHashMap<>();
    /** Configured protocol endpoints that execute inside an enclosing root. */
    final Set<String> nestedContextEndpoints = new LinkedHashSet<>();
    final List<Map<String, Object>> regions = new ArrayList<>();
    final List<Map<String, Object>> regionEdges = new ArrayList<>();
    final Map<String, Object> targetResolved = new LinkedHashMap<>();
}
