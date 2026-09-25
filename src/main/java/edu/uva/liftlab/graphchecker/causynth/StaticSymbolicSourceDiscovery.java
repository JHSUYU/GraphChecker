package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.strings;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/** The {@code symbolize} hook's PUBLISH sites: one declaration per source. */
final class StaticSymbolicSourceDiscovery {
    private static final String HOOK_CLASS_SIMPLE_NAME =
            "CausynthSymbolicSource";
    private static final String HOOK_METHOD = "symbolize";

    private StaticSymbolicSourceDiscovery() {
    }

    /** Attaches declarations to every region that can execute the hook. */
    static void discover(StaticProgram program) throws IOException {
        if (program.regions.isEmpty()) return;
        Set<String> regionRoots = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            regionRoots.addAll(strings(Arrays.asList(
                    region.get("rootMethod"), region.get("anchorMethod"))));
        }
        Set<String> cutBoundaries = new LinkedHashSet<>(
                program.communicationCallSiteCallees);
        for (Map<String, Object> region : program.regions) {
            discoverRegion(region, regionRoots, cutBoundaries);
        }
        Set<String> traceMethods = new LinkedHashSet<>(program.traceMethods);
        for (Map<String, Object> region : program.regions) {
            traceMethods.addAll(strings(region.get(
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
        List<String> initial = strings(region.get("methods"));
        Collections.sort(initial);
        work.addAll(initial);
        Set<String> seen = new LinkedHashSet<>();
        Map<String, Map<String, Object>> bySource = new LinkedHashMap<>();
        List<JsonObject> phases = new ArrayList<>();
        Set<String> phaseIdentities = new LinkedHashSet<>();
        Set<String> phaseTraceMethods = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            String signature = work.removeFirst();
            if (!seen.add(signature)) continue;
            SootMethod method = concreteMethod(signature);
            Body body = CausynthStaticFacts.activeBody(method);
            if (body == null) continue;
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
                    String sourceId = text(declaration.get("sourceId"));
                    JsonObject phase;
                    try {
                        phase = ConfiguredSourcePhaseContract.declaration(
                                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                                sourceId,
                                text(declaration.get("fieldSignature")),
                                signature, unitIndex);
                    } catch (IllegalArgumentException rejected) {
                        throw malformed(method, unitIndex,
                                rejected.getMessage());
                    }
                    if (phaseIdentities.add(sourceId + "\n"
                            + JsonFields.optionalString(phase, "siteId"))) {
                        phases.add(phase);
                        phaseTraceMethods.add(signature);
                    }
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
            region.put(ConfiguredSourcePhaseContract.DECLARATION_FIELD,
                    phases);
            List<String> traced = new ArrayList<>(phaseTraceMethods);
            Collections.sort(traced);
            region.put(ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD,
                    traced);
        }
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
                + "declaration at "
                + SiteId.of(method.getSignature(), unitIndex)
                + ": " + detail);
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
        SootMethod method = CausynthStaticFacts.method(signature);
        return method != null && method.isConcrete()
                && method.getDeclaringClass().isApplicationClass()
                ? method : null;
    }
}
