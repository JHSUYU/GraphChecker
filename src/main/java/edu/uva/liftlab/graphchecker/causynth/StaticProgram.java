package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/** Canonical in-memory artifact set for one static analysis run. */
final class StaticProgram {
    final List<Map<String, Object>> edges = new ArrayList<>();
    final List<String> traceMethods = new ArrayList<>();
    final List<Map<String, Object>> regions = new ArrayList<>();
    final List<Map<String, Object>> regionEdges = new ArrayList<>();
    boolean coverageComplete;
    final Map<String, Object> targetResolved = new LinkedHashMap<>();
}
