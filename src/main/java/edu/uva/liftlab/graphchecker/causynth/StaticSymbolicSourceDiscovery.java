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
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;
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

/**
 * The configured sources each region can mint (SYMBOL-SCOPE §4.3), from the
 * text it runs -- its methods and their application callees: a tree's
 * {@code CausynthSymbolicSource.symbolize} call (one hook site per source
 * per region), and the engine's read ({@code getfield}) of a configuration
 * field {@link ConfigRoots} declares, every one of them.  A field a tree's
 * hook mints is the hook's: no read of it is the engine's.  The
 * configuration reads no root mints are published beside, as catalog gaps
 * ({@link ConfigRoots#gaps}).
 */
final class StaticSymbolicSourceDiscovery {
    private static final String HOOK_CLASS_SIMPLE_NAME =
            "CausynthSymbolicSource";
    private static final String HOOK_METHOD = "symbolize";

    private StaticSymbolicSourceDiscovery() {
    }

    /** One mint site a region's text holds. */
    private static final class Site {
        final Map<String, Object> declaration;
        final JsonObject phase;
        final String method;

        Site(Map<String, Object> declaration, JsonObject phase,
             String method) {
            this.declaration = declaration;
            this.phase = phase;
            this.method = method;
        }

        String field() {
            return text(declaration.get("fieldSignature"));
        }

        boolean hook() {
            return StaticSymbolicSourceDeclaration.AUTHORITY.equals(
                    text(declaration.get("authority")));
        }
    }

    /**
     * Attaches declarations to every region that can execute a site, and
     * names the configuration reads left concrete.
     *
     * @return the configuration field reads declared, each a plant of the
     *         world's value ({@link ConfigRoots#keyRows})
     */
    static Set<String> discover(StaticProgram program, ConfigRoots config)
            throws IOException {
        program.communicationGaps.addAll(config.gaps());
        Set<String> planted = new LinkedHashSet<>();
        if (program.regions.isEmpty()) return planted;
        Set<String> regionRoots = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            regionRoots.addAll(strings(Arrays.asList(
                    region.get("rootMethod"), region.get("anchorMethod"))));
        }
        Set<String> cutBoundaries = new LinkedHashSet<>(
                program.communicationCallSiteCallees);
        Map<Map<String, Object>, List<Site>> sites = new LinkedHashMap<>();
        Set<String> hooked = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            List<Site> found = sitesOf(region, regionRoots, cutBoundaries,
                    config);
            for (Site site : found) {
                if (site.hook()) hooked.add(site.field());
            }
            sites.put(region, found);
        }
        for (Map.Entry<Map<String, Object>, List<Site>> region
                : sites.entrySet()) {
            attach(region.getKey(), region.getValue(), hooked);
            for (Site site : region.getValue()) {
                if (!site.hook() && !hooked.contains(site.field())) {
                    planted.add(JsonFields.optionalString(site.phase,
                            "siteId"));
                }
            }
        }
        return planted;
    }

    /** The mint sites one region's text holds, in walk order. */
    private static List<Site> sitesOf(
            Map<String, Object> region, Set<String> regionRoots,
            Set<String> cutBoundaries, ConfigRoots config)
            throws IOException {
        Deque<String> work = new ArrayDeque<>();
        List<String> initial = strings(region.get("methods"));
        Collections.sort(initial);
        work.addAll(initial);
        Set<String> seen = new LinkedHashSet<>();
        List<Site> found = new ArrayList<>();
        while (!work.isEmpty()) {
            String signature = work.removeFirst();
            if (!seen.add(signature)) continue;
            SootMethod method = concreteMethod(signature);
            Body body = CausynthStaticFacts.activeBody(method);
            if (body == null) continue;
            int unitIndex = 0;
            for (Unit unit : body.getUnits()) {
                Site read = configRead(method, unit, unitIndex, config);
                if (read != null) found.add(read);
                if (unit instanceof Stmt
                        && ((Stmt) unit).containsInvokeExpr()) {
                    InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
                    if (symbolizeHook(invoke)) {
                        found.add(hook(method, invoke, unitIndex));
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
                }
                unitIndex++;
            }
        }
        return found;
    }

    /** The region's declarations and phases, a hooked field's reads left
     *  to its hook. */
    private static void attach(Map<String, Object> region, List<Site> sites,
                               Set<String> hooked) throws IOException {
        Map<String, Map<String, Object>> bySource = new LinkedHashMap<>();
        List<JsonObject> phases = new ArrayList<>();
        Set<String> phaseIdentities = new LinkedHashSet<>();
        Set<String> phaseTraceMethods = new LinkedHashSet<>();
        for (Site site : sites) {
            if (!site.hook() && hooked.contains(site.field())) continue;
            merge(bySource, site, region);
            if (phaseIdentities.add(text(site.declaration.get("sourceId"))
                    + "\n" + JsonFields.optionalString(site.phase,
                    "siteId"))) {
                phases.add(site.phase);
                phaseTraceMethods.add(site.method);
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

    /** A read of a declared configuration field at this unit, or null. */
    private static Site configRead(SootMethod method, Unit unit,
                                   int unitIndex, ConfigRoots config) {
        if (!(unit instanceof AssignStmt) || !(((AssignStmt) unit)
                .getRightOp() instanceof InstanceFieldRef)) {
            return null;
        }
        String field = CausynthStaticFacts.declaredFieldSignature(
                ((InstanceFieldRef) ((AssignStmt) unit).getRightOp())
                        .getFieldRef());
        ConfigRoots.Source source = config.field(field);
        if (source == null) return null;
        String signature = method.getSignature();
        return new Site(declaration(
                StaticSymbolicSourceDeclaration.CONFIG_AUTHORITY,
                source.sourceId, field, signature, unitIndex),
                ConfiguredSourcePhaseContract.configDeclaration(
                        source.sourceId, field, signature, unitIndex,
                        source.domainMin, source.domainMax), signature);
    }

    /** A tree's hook call. */
    private static Site hook(SootMethod method, InvokeExpr invoke,
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
        String signature = method.getSignature();
        try {
            return new Site(declaration(
                    StaticSymbolicSourceDeclaration.AUTHORITY, sourceId,
                    field, signature, unitIndex),
                    ConfiguredSourcePhaseContract.declaration(sourceId,
                            field, signature, unitIndex), signature);
        } catch (IllegalArgumentException rejected) {
            throw malformed(method, unitIndex, rejected.getMessage());
        }
    }

    private static Map<String, Object> declaration(
            String authority, String sourceId, String field, String method,
            int unitIndex) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("schemaVersion",
                StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
        result.put("kind", StaticSymbolicSourceDeclaration.KIND);
        result.put("authority", authority);
        result.put("sourceId", sourceId);
        result.put("fieldSignature", field);
        result.put("declarationMethod", method);
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

    /**
     * One declaration per source and region: a source one field, a hook's
     * one site.  A configuration source is read at every site that reads
     * its field; its declaration names the first.
     */
    private static void merge(
            Map<String, Map<String, Object>> bySource, Site site,
            Map<String, Object> region) throws IOException {
        Map<String, Object> declaration = site.declaration;
        String sourceId = text(declaration.get("sourceId"));
        Map<String, Object> prior = bySource.putIfAbsent(
                sourceId, declaration);
        if (prior == null) return;
        if (!text(prior.get("fieldSignature")).equals(site.field())) {
            throw new IOException("region "
                    + text(region.get("regionId"))
                    + " gives symbolic source " + sourceId
                    + " two fields");
        }
        if (site.hook() && (!text(prior.get("declarationMethod")).equals(
                text(declaration.get("declarationMethod")))
                || !text(prior.get("declarationUnitIndex")).equals(
                text(declaration.get("declarationUnitIndex"))))) {
            throw new IOException("region "
                    + text(region.get("regionId"))
                    + " declares symbolic source " + sourceId
                    + " at more than one hook site");
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
