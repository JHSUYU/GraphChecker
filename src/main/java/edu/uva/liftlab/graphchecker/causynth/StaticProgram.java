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
     * MAIN_ENTRY, or RPC_HANDLER. Constructors and ordinary helpers never
     * appear here.
     */
    final Map<String, String> executionContextAuthorities =
            new LinkedHashMap<>();
    final List<Map<String, Object>> regions = new ArrayList<>();
    final List<Map<String, Object>> regionEdges = new ArrayList<>();
    final Map<String, Object> targetResolved = new LinkedHashMap<>();
    /**
     * Static communication discovery: one row per target-selected
     * communication call site ({@code COMMUNICATION_CALL_SITE}) and one row
     * per named gap.  The schema is
     * {@link edu.uva.liftlab.graphchecker.contract
     * .CommunicationCatalogContract}.
     */
    final List<Map<String, Object>> communicationCallSites =
            new ArrayList<>();
    /** One row per retained loop of a selected method. */
    final List<Map<String, Object>> retainedLoops = new ArrayList<>();
    final List<Map<String, Object>> communicationGaps = new ArrayList<>();
    /**
     * Callee signatures that are communication boundaries in the selected
     * slice.  This is the sole authority for where a demand walk stops; it
     * is discovered from the slice, never declared.
     */
    final Set<String> communicationCallSiteCallees = new LinkedHashSet<>();
    /**
     * Static-only implementation frames removed before region closure.
     * Never serialized: artifacts contain only the resulting application
     * envelope, not a second classification schema for excluded methods.
     */
    final Set<String> regionEnvelopeExclusions = new LinkedHashSet<>();
}
