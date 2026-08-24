package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;

import java.io.IOException;
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

/** Discovers exact symbolic-source declarations from explicit Java hooks. */
final class StaticSymbolicSourceDiscovery {
    private static final String HOOK_CLASS_SIMPLE_NAME =
            "CausynthSymbolicSource";
    private static final String HOOK_METHOD = "symbolize";
    private static final String SELECTOR_METHOD = "selectedIntValue";

    private StaticSymbolicSourceDiscovery() {
    }

    /**
     * Attaches declarations to every region that can execute the hook.
     * Direct application helpers are followed because a source declaration
     * is normally kept in one small helper shared by several RPC handlers.
     * Other region roots and communication cuts remain hard boundaries.
     */
    static void discover(StaticProgram program) throws IOException {
        if (program == null || program.regions.isEmpty()) return;
        Set<String> regionRoots = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            addText(regionRoots, region.get("rootMethod"));
            addText(regionRoots, region.get("anchorMethod"));
        }
        Set<String> cutBoundaries = new LinkedHashSet<>(
                program.communicationCallSiteCallees);
        for (Map<String, Object> region : program.regions) {
            discoverRegion(region, regionRoots, cutBoundaries);
        }
        Set<String> traceMethods = new LinkedHashSet<>(program.traceMethods);
        for (Map<String, Object> region : program.regions) {
            traceMethods.addAll(texts(region.get(
                    ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD)));
        }
        program.traceMethods.clear();
        program.traceMethods.addAll(traceMethods);
        Collections.sort(program.traceMethods);
    }

    private static void discoverRegion(
            Map<String, Object> region, Set<String> regionRoots,
            Set<String> cutBoundaries) throws IOException {
        Deque<String> work = new ArrayDeque<>();
        List<String> initial = texts(region.get("methods"));
        Collections.sort(initial);
        work.addAll(initial);
        Set<String> seen = new LinkedHashSet<>();
        Map<String, Map<String, Object>> bySource = new LinkedHashMap<>();
        List<Map<String, Object>> phases = new ArrayList<>();
        Set<String> phaseIdentities = new LinkedHashSet<>();
        Set<String> phaseTraceMethods = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            String signature = work.removeFirst();
            if (!seen.add(signature)) continue;
            SootMethod method = concreteMethod(signature);
            if (method == null) continue;
            Body body;
            try {
                body = method.retrieveActiveBody();
            } catch (RuntimeException unavailable) {
                continue;
            }
            int unitIndex = 0;
            for (Unit unit : body.getUnits()) {
                if (!(unit instanceof Stmt)
                        || !((Stmt) unit).containsInvokeExpr()) {
                    unitIndex++;
                    continue;
                }
                InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
                if (symbolizeHook(invoke)) {
                    Map<String, Object> declaration = declaration(
                            method, invoke, unitIndex);
                    merge(bySource, declaration, region);
                    addPhase(phases, phaseIdentities, phaseTraceMethods,
                            ConfiguredSourcePhaseContract.Phase.PUBLISH,
                            text(declaration.get("sourceId")),
                            text(declaration.get("fieldSignature")),
                            method, unitIndex);
                } else if (selectorHook(invoke)) {
                    addPhase(phases, phaseIdentities, phaseTraceMethods,
                            ConfiguredSourcePhaseContract.Phase.CONSUME,
                            selectorSourceId(method, invoke, unitIndex), "",
                            method, unitIndex);
                } else {
                    SootMethod callee = concreteCallee(invoke);
                    if (callee != null) {
                        String calleeSignature = callee.getSignature();
                        if (!cutBoundaries.contains(calleeSignature)
                                && (!regionRoots.contains(calleeSignature)
                                || initial.contains(calleeSignature))) {
                            work.addLast(calleeSignature);
                        }
                    }
                }
                unitIndex++;
            }
        }
        if (!bySource.isEmpty()) {
            region.put(StaticSymbolicSourceDeclaration.FIELD,
                    new ArrayList<>(bySource.values()));
        }
        if (!phases.isEmpty()) {
            for (Map<String, Object> phase : phases) {
                if (!ConfiguredSourcePhaseContract.Phase.CONSUME.name().equals(
                        text(phase.get("phase")))) {
                    continue;
                }
                Map<String, Object> source = bySource.get(
                        text(phase.get("sourceId")));
                if (source != null) {
                    phase.put("fieldSignature",
                            text(source.get("fieldSignature")));
                }
            }
            region.put(ConfiguredSourcePhaseContract.DECLARATION_FIELD,
                    phases);
            List<String> traced = new ArrayList<>(phaseTraceMethods);
            Collections.sort(traced);
            region.put(ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD,
                    traced);
        }
    }

    private static void addPhase(
            List<Map<String, Object>> phases, Set<String> identities,
            Set<String> traceMethods,
            ConfiguredSourcePhaseContract.Phase phase,
            String sourceId, String fieldSignature,
            SootMethod method, int unitIndex) throws IOException {
        final Map<String, Object> declaration;
        try {
            declaration = ConfiguredSourcePhaseContract.declaration(
                    phase, sourceId, fieldSignature,
                    method.getSignature(), unitIndex);
        } catch (IllegalArgumentException malformed) {
            throw malformed(method, unitIndex, malformed.getMessage());
        }
        String identity = phase.name() + "\n" + sourceId + "\n"
                + declaration.get("siteId");
        if (identities.add(identity)) {
            phases.add(declaration);
            traceMethods.add(method.getSignature());
        }
    }

    private static String selectorSourceId(
            SootMethod method, InvokeExpr invoke, int unitIndex)
            throws IOException {
        if (invoke.getArgCount() != 1
                || !(invoke.getArg(0) instanceof StringConstant)) {
            throw malformed(method, unitIndex,
                    "selector sourceId must be a string constant");
        }
        String sourceId = ((StringConstant) invoke.getArg(0)).value.trim();
        if (sourceId.isEmpty()) {
            throw malformed(method, unitIndex,
                    "selector sourceId must be non-empty");
        }
        return sourceId;
    }

    private static Map<String, Object> declaration(
            SootMethod method, InvokeExpr invoke,
            int unitIndex) throws IOException {
        if (invoke.getArgCount() != 3
                || !(invoke.getArg(0) instanceof StringConstant)
                || !(invoke.getArg(2) instanceof StringConstant)) {
            throw malformed(method, unitIndex,
                    "sourceId and fieldSignature must be string constants");
        }
        Value owner = invoke.getArg(1);
        // The exact owner is selected by the application at this hook.  It
        // may be the region receiver, or an object first resolved from an
        // array/Map.  Requiring `this` made those exact member-field sources
        // impossible and encouraged whole-container symbolization instead.
        // A local is stable for this Jimple statement; runtime occurrence
        // admission then requires this sourceId to resolve to one object only.
        if (!(owner instanceof Local)) {
            throw malformed(method, unitIndex,
                    "owner must be an explicit local object");
        }
        String sourceId = ((StringConstant) invoke.getArg(0)).value.trim();
        String field = ((StringConstant) invoke.getArg(2)).value.trim();
        if (sourceId.isEmpty()
                || FieldPathSpec.declaredField(field) == null) {
            throw malformed(method, unitIndex,
                    "sourceId or fieldSignature is malformed");
        }
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("schemaVersion",
                StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
        result.put("kind", StaticSymbolicSourceDeclaration.KIND);
        result.put("authority", StaticSymbolicSourceDeclaration.AUTHORITY);
        result.put("sourceId", sourceId);
        result.put("fieldSignature", field);
        result.put("declarationMethod", method.getSignature());
        result.put("declarationUnitIndex", unitIndex);
        return result;
    }

    private static IOException malformed(
            SootMethod method, int unitIndex, String detail) {
        return new IOException("invalid CausynthSymbolicSource.symbolize "
                + "declaration at " + method.getSignature() + "#u"
                + unitIndex + ": " + detail);
    }

    private static void merge(
            Map<String, Map<String, Object>> bySource,
            Map<String, Object> declaration, Map<String, Object> region)
            throws IOException {
        String sourceId = text(declaration.get("sourceId"));
        Map<String, Object> prior = bySource.putIfAbsent(
                sourceId, declaration);
        if (prior != null) {
            if (!text(prior.get("fieldSignature")).equals(
                    text(declaration.get("fieldSignature")))) {
                throw new IOException("region "
                        + text(region.get("regionId"))
                        + " gives symbolic source " + sourceId
                        + " two fields");
            }
            if (!text(prior.get("declarationMethod")).equals(
                    text(declaration.get("declarationMethod")))
                    || !text(prior.get("declarationUnitIndex")).equals(
                    text(declaration.get("declarationUnitIndex")))) {
                throw new IOException("region "
                        + text(region.get("regionId"))
                        + " declares symbolic source " + sourceId
                        + " at more than one hook site");
            }
        }
    }

    private static boolean symbolizeHook(InvokeExpr invoke) {
        if (invoke == null || !HOOK_METHOD.equals(
                invoke.getMethodRef().name())
                || invoke.getMethodRef().parameterTypes().size() != 3) {
            return false;
        }
        String owner = invoke.getMethodRef().declaringClass().getName();
        int separator = owner.lastIndexOf('.');
        String simple = separator < 0 ? owner : owner.substring(separator + 1);
        List<soot.Type> parameters = invoke.getMethodRef().parameterTypes();
        return HOOK_CLASS_SIMPLE_NAME.equals(simple)
                && "java.lang.String".equals(parameters.get(0).toString())
                && "java.lang.Object".equals(parameters.get(1).toString())
                && "java.lang.String".equals(parameters.get(2).toString());
    }

    private static boolean selectorHook(InvokeExpr invoke) {
        if (invoke == null || !SELECTOR_METHOD.equals(
                invoke.getMethodRef().name())
                || invoke.getMethodRef().parameterTypes().size() != 1) {
            return false;
        }
        String owner = invoke.getMethodRef().declaringClass().getName();
        int separator = owner.lastIndexOf('.');
        String simple = separator < 0 ? owner : owner.substring(separator + 1);
        return HOOK_CLASS_SIMPLE_NAME.equals(simple)
                && "java.lang.String".equals(invoke.getMethodRef()
                .parameterTypes().get(0).toString());
    }

    private static SootMethod concreteCallee(InvokeExpr invoke) {
        try {
            SootMethod method = invoke.getMethodRef().resolve();
            return method != null && method.isConcrete()
                    && method.getDeclaringClass().isApplicationClass()
                    ? method : null;
        } catch (RuntimeException unresolved) {
            return null;
        }
    }

    private static SootMethod concreteMethod(String signature) {
        try {
            SootMethod method = Scene.v().getMethod(signature);
            return method != null && method.isConcrete()
                    && method.getDeclaringClass().isApplicationClass()
                    ? method : null;
        } catch (RuntimeException unresolved) {
            return null;
        }
    }

    private static void addText(Set<String> output, Object value) {
        String encoded = text(value);
        if (!encoded.isEmpty()) output.add(encoded);
    }

    private static List<String> texts(Object value) {
        List<String> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object element : (Collection<?>) value) {
                String encoded = text(element);
                if (!encoded.isEmpty()) result.add(encoded);
            }
        }
        return result;
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value).trim();
    }
}
