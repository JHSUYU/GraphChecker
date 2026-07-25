package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Mutable artifact model produced by the static Causynth analysis.
 *
 * <p>This package-private carrier deliberately contains no analysis logic. It
 * gives the pipeline stages and the artifact writer a shared boundary without
 * making either component depend on the other's implementation details.</p>
 */
final class CausynthAnalysisResult {
    final List<Map<String, Object>> edges = new ArrayList<>();
    final List<Map<String, Object>> traceMethods = new ArrayList<>();
    final List<Map<String, Object>> symbolicPlan = new ArrayList<>();
    final List<Map<String, Object>> symbolicRegions = new ArrayList<>();
    final List<Map<String, Object>> symbolicRegionEdges = new ArrayList<>();
    final Map<String, Object> symbolicCoverage = new LinkedHashMap<>();
    final Map<String, Object> targetResolved = new LinkedHashMap<>();
}
