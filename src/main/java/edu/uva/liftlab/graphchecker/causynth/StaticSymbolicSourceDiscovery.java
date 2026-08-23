package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
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
            Local thisLocal = method.isStatic() ? null : safeThis(body);
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
                            method, thisLocal, invoke, unitIndex);
                    merge(bySource, declaration, region);
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
    }

    private static Map<String, Object> declaration(
            SootMethod method, Local thisLocal, InvokeExpr invoke,
            int unitIndex) throws IOException {
        if (invoke.getArgCount() != 3
                || !(invoke.getArg(0) instanceof StringConstant)
                || !(invoke.getArg(2) instanceof StringConstant)) {
            throw malformed(method, unitIndex,
                    "sourceId and fieldSignature must be string constants");
        }
        Value owner = invoke.getArg(1);
        if (thisLocal == null || !thisLocal.equals(owner)) {
            throw malformed(method, unitIndex,
                    "owner must be the declaring method's this object");
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
        if (prior != null && !text(prior.get("fieldSignature")).equals(
                text(declaration.get("fieldSignature")))) {
            throw new IOException("region " + text(region.get("regionId"))
                    + " gives symbolic source " + sourceId
                    + " two fields");
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

    private static Local safeThis(Body body) {
        try {
            return body.getThisLocal();
        } catch (RuntimeException absent) {
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
