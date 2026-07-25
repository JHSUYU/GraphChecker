package edu.uva.liftlab.graphchecker.causynth;

import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.ParameterRef;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Assembles same-thread symbolic regions and their static entry contracts. */
final class SymbolicRegionAssemblyStage {
    private static final int MAX_ROOT_ARGUMENT_PATH_FIELDS = 64;

    private SymbolicRegionAssemblyStage() {
    }

    static void assemble(CausynthAnalysisResult result) {
        SymbolicRegionPlanner.Result planned = SymbolicRegionPlanner.plan(
                result.edges, result.symbolicPlan);
        enrichHeapMutationGuardMetadata(planned.regions, result.edges);
        addArgumentPathFieldContracts(planned.regions);
        result.symbolicRegions.addAll(planned.regions);
        result.symbolicRegionEdges.addAll(planned.regionEdges);
        result.symbolicCoverage.putAll(planned.coverage);
    }

    /** Reattaches per-site mutation guards to compact causal-edge rows. */
    static void enrichHeapMutationGuardMetadata(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> analysisEdges) {
        Map<String, Map<String, Object>> byId = new LinkedHashMap<>();
        for (Map<String, Object> edge : analysisEdges) {
            if ("heap_mutation_path_guard".equals(
                    stringValue(edge.get("kind")))) {
                byId.put(stringValue(edge.get("id")), edge);
            }
        }
        for (Map<String, Object> region : regions) {
            Object slicesValue = region.get("outputSlices");
            if (!(slicesValue instanceof Collection)) {
                continue;
            }
            for (Object sliceValue : (Collection<?>) slicesValue) {
                if (!(sliceValue instanceof Map)) {
                    continue;
                }
                Map<?, ?> slice = (Map<?, ?>) sliceValue;
                Object referencesValue = slice.get("causalEdges");
                if (!(referencesValue instanceof Collection)) {
                    continue;
                }
                for (Object referenceValue
                        : (Collection<?>) referencesValue) {
                    if (!(referenceValue instanceof Map)) {
                        continue;
                    }
                    @SuppressWarnings("unchecked")
                    Map<String, Object> reference =
                            (Map<String, Object>) referenceValue;
                    Map<String, Object> source = byId.get(stringValue(
                            reference.get("edgeId")));
                    if (source == null) {
                        continue;
                    }
                    copyIfPresent(source, reference, "guardSiteId");
                    copyIfPresent(source, reference,
                            "guardedMutationSiteId");
                    copyIfPresent(source, reference, "requiredOutcome");
                    copyIfPresent(source, reference,
                            "guardedMutationCount");
                    copyIfPresent(source, reference,
                            "guardedMutationsAuthority");
                    copyIfPresent(source, reference, "guardedMutations");
                }
            }
        }
    }

    private static void copyIfPresent(Map<String, Object> source,
                                      Map<String, Object> target,
                                      String field) {
        if (source.containsKey(field)) {
            target.put(field, source.get(field));
        }
    }

    /**
     * Records root-argument fields that can influence a branch executed after
     * a candidate region entry.
     */
    static void addArgumentPathFieldContracts(
            List<Map<String, Object>> regions) {
        for (Map<String, Object> region : regions) {
            Object methodsValue = region.get("methods");
            if (!(methodsValue instanceof Collection)) {
                continue;
            }
            List<Map<String, Object>> contracts = new ArrayList<>();
            for (Object methodValue : (Collection<?>) methodsValue) {
                String signature = stringValue(methodValue);
                if (signature.isEmpty()) {
                    continue;
                }
                try {
                    SootMethod method = Scene.v().getMethod(signature);
                    if (method != null && method.isConcrete()) {
                        contracts.addAll(argumentPathFieldContracts(method));
                    }
                } catch (RuntimeException ignored) {
                    // Dynamic getter observations remain available when a
                    // candidate body cannot be loaded statically.
                }
            }
            if (!contracts.isEmpty()) {
                region.put("argumentPathFields", contracts);
            }
        }
    }

    private static List<Map<String, Object>> argumentPathFieldContracts(
            SootMethod method) {
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return Collections.emptyList();
        }
        List<Unit> units = snapshotUnits(body);
        Map<Local, Set<Integer>> argumentAliases = new LinkedHashMap<>();
        Map<Local, Set<ArgumentFieldOrigin>> fieldOrigins =
                new LinkedHashMap<>();
        for (Unit unit : units) {
            if (!(unit instanceof IdentityStmt)) {
                continue;
            }
            IdentityStmt identity = (IdentityStmt) unit;
            if (identity.getLeftOp() instanceof Local
                    && identity.getRightOp() instanceof ParameterRef) {
                addValue(argumentAliases, (Local) identity.getLeftOp(),
                        ((ParameterRef) identity.getRightOp()).getIndex());
            }
        }

        boolean changed = true;
        int rounds = 0;
        while (changed && rounds++ <= units.size() + 1) {
            changed = false;
            for (Unit unit : units) {
                if (!(unit instanceof AssignStmt)) {
                    continue;
                }
                AssignStmt assignment = (AssignStmt) unit;
                if (!(assignment.getLeftOp() instanceof Local)) {
                    continue;
                }
                Local left = (Local) assignment.getLeftOp();
                Value right = assignment.getRightOp();
                changed |= addValues(argumentAliases, left,
                        directArgumentAliases(right, argumentAliases));

                Set<ArgumentFieldOrigin> origins = new LinkedHashSet<>();
                for (ValueBox box : right.getUseBoxes()) {
                    if (box.getValue() instanceof Local) {
                        origins.addAll(values(fieldOrigins,
                                (Local) box.getValue()));
                    }
                }
                if (right instanceof InstanceFieldRef) {
                    InstanceFieldRef field = (InstanceFieldRef) right;
                    if (field.getBase() instanceof Local) {
                        for (Integer index : values(argumentAliases,
                                (Local) field.getBase())) {
                            origins.add(new ArgumentFieldOrigin(index,
                                    field.getFieldRef().name()));
                        }
                    }
                }
                if (right instanceof InstanceInvokeExpr) {
                    InstanceInvokeExpr invoke = (InstanceInvokeExpr) right;
                    if (invoke.getBase() instanceof Local) {
                        String field = getterFieldName(invoke);
                        if (!field.isEmpty()) {
                            for (Integer index : values(argumentAliases,
                                    (Local) invoke.getBase())) {
                                origins.add(new ArgumentFieldOrigin(index,
                                        field));
                            }
                        }
                    }
                }
                changed |= addValues(fieldOrigins, left, origins);
            }
        }

        Map<Integer, Set<String>> fieldsByArgument = new LinkedHashMap<>();
        Map<Integer, Set<String>> sitesByArgument = new LinkedHashMap<>();
        for (int unitIndex = 0; unitIndex < units.size(); unitIndex++) {
            Unit unit = units.get(unitIndex);
            if (!(unit instanceof IfStmt)) {
                continue;
            }
            Set<ArgumentFieldOrigin> origins = new LinkedHashSet<>();
            for (ValueBox box : ((IfStmt) unit).getCondition().getUseBoxes()) {
                if (box.getValue() instanceof Local) {
                    origins.addAll(values(fieldOrigins,
                            (Local) box.getValue()));
                }
            }
            for (ArgumentFieldOrigin origin : origins) {
                addValue(fieldsByArgument, origin.argumentIndex,
                        origin.field);
                addValue(sitesByArgument, origin.argumentIndex,
                        stableSiteId(method.getSignature(), unitIndex,
                                "branch"));
            }
        }

        List<Map<String, Object>> result = new ArrayList<>();
        for (Integer argumentIndex : fieldsByArgument.keySet()) {
            result.add(object(
                    "method", method.getSignature(),
                    "argumentIndex", argumentIndex,
                    "fields", sortedLimited(
                            fieldsByArgument.get(argumentIndex)),
                    "branchSites", sortedLimited(
                            sitesByArgument.get(argumentIndex)),
                    "authority", "STATIC_ROOT_BRANCH_DATAFLOW"));
        }
        return result;
    }

    private static Set<Integer> directArgumentAliases(
            Value value, Map<Local, Set<Integer>> aliases) {
        if (value instanceof Local) {
            return values(aliases, (Local) value);
        }
        if (value instanceof CastExpr
                && ((CastExpr) value).getOp() instanceof Local) {
            return values(aliases, (Local) ((CastExpr) value).getOp());
        }
        return Collections.emptySet();
    }

    private static String getterFieldName(InstanceInvokeExpr invoke) {
        if (invoke.getArgCount() != 0) {
            return "";
        }
        String name = invoke.getMethodRef().name();
        String stem;
        if (name.startsWith("get") && name.length() > 3) {
            stem = name.substring(3);
        } else if (name.startsWith("is") && name.length() > 2) {
            stem = name.substring(2);
        } else {
            return "";
        }
        return Character.toLowerCase(stem.charAt(0)) + stem.substring(1);
    }

    private static <K, V> Set<V> values(Map<K, Set<V>> values, K key) {
        Set<V> result = values.get(key);
        return result == null ? Collections.emptySet() : result;
    }

    private static <K, V> boolean addValue(Map<K, Set<V>> values,
                                            K key, V value) {
        return values.computeIfAbsent(key, ignored -> new LinkedHashSet<>())
                .add(value);
    }

    private static <K, V> boolean addValues(Map<K, Set<V>> values,
                                             K key,
                                             Collection<V> additions) {
        return additions != null && !additions.isEmpty()
                && values.computeIfAbsent(key,
                ignored -> new LinkedHashSet<>()).addAll(additions);
    }

    private static List<Unit> snapshotUnits(Body body) {
        List<Unit> units = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            units.add(unit);
        }
        return units;
    }

    private static String stableSiteId(String method, int unitIndex,
                                       String kind) {
        if (unitIndex >= 0) {
            return method + "#u" + unitIndex;
        }
        return method + "#synthetic:"
                + (kind == null || kind.trim().isEmpty()
                ? "edge" : kind.trim());
    }

    private static List<String> sortedLimited(Set<String> values) {
        List<String> sorted = new ArrayList<>(values);
        Collections.sort(sorted);
        if (sorted.size() <= MAX_ROOT_ARGUMENT_PATH_FIELDS) {
            return sorted;
        }
        return new ArrayList<>(sorted.subList(0,
                MAX_ROOT_ARGUMENT_PATH_FIELDS));
    }

    private static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static Map<String, Object> object(Object... keyValues) {
        Map<String, Object> map = new LinkedHashMap<>();
        for (int i = 0; i + 1 < keyValues.length; i += 2) {
            map.put(String.valueOf(keyValues[i]), keyValues[i + 1]);
        }
        return map;
    }

    private static final class ArgumentFieldOrigin {
        private final int argumentIndex;
        private final String field;

        private ArgumentFieldOrigin(int argumentIndex, String field) {
            this.argumentIndex = argumentIndex;
            this.field = field;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof ArgumentFieldOrigin)) {
                return false;
            }
            ArgumentFieldOrigin that = (ArgumentFieldOrigin) other;
            return argumentIndex == that.argumentIndex
                    && field.equals(that.field);
        }

        @Override
        public int hashCode() {
            return 31 * argumentIndex + field.hashCode();
        }
    }
}
