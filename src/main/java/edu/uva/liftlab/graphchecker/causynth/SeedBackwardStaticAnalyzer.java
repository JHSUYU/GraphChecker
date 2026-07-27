package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.UnitGraph;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ConstructorCallsite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ConstructorParam;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ExceptionConstruction;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ExceptionGuard;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.Fact;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.FieldWrite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.InstanceFieldAccess;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.MethodCallsite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.actualInvokeArgs;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.fieldOwner;


/** Static backward data-flow analysis from one annotated exception target. */
final class SeedBackwardStaticAnalyzer {
    private static final Logger LOG = LoggerFactory.getLogger(
            CausynthPipeline.class);
    private static final int DEFAULT_MAX_METHODS = 1000;
    private static final int DEFAULT_MAX_EDGES = 50000;
    private static final int MAX_RPC_TARGETS_PER_CALL = 6;
    private static final int MAX_DISPATCH_TARGETS_PER_CALL = 8;
    private static final int MAX_RUNTIME_RECURSIVE_METHODS = 128;
    private static final int MAX_CONSTRUCTOR_CALLERS_PER_PARAM = 80;
    private static final int MAX_METHOD_CALLERS_PER_METHOD = 200;
    private static final int MAX_FIELD_WRITERS_PER_FIELD = 80;
    private static final int MAX_FIELD_PATH_DEPTH = 4;
    private static final Pattern LOCAL_NAME_PATTERN =
            Pattern.compile("[$]?[A-Za-z_][A-Za-z0-9_]*");
    private static final Pattern CAST_LOCAL_PATTERN =
            Pattern.compile("\\)\\s*([$]?[A-Za-z_][A-Za-z0-9_]*)$");
    private static final Pattern INVOKE_BASE_PATTERN = Pattern.compile(
            "(?:virtualinvoke|interfaceinvoke|specialinvoke)\\s+"
                    + "([$]?[A-Za-z_][A-Za-z0-9_]*)\\.<");
    private static final Pattern CONSTRUCTOR_PARAMETER_PATTERN =
            Pattern.compile(">\\.param(\\d+):");
    private static final Pattern FIELD_PATTERN =
            Pattern.compile("<[^:]+:\\s+.+\\s+[^\\s()]+>");
    private static final Pattern METHOD_SIGNATURE_PATTERN = Pattern.compile(
            "<([^:]+):\\s+(.+)\\s+([^\\s(]+)\\((.*)\\)>");
    private final CausynthTargetContext target;
    private final int maxMethods;
    private final int maxEdges;
    private final Map<String, SootClass> classesByName = new LinkedHashMap<>();
    private final Map<String, SootMethod> methodsBySignature = new LinkedHashMap<>();
    private final Map<String, List<SootMethod>> concreteMethodsBySubSignature =
            new LinkedHashMap<>();
    private final Map<String, List<Fact>> factsByMethod = new LinkedHashMap<>();
    private final Map<String, MethodControlFlow> controlFlowByMethod =
            new LinkedHashMap<>();
    private final Map<String, List<String>> rpcTargetsBySource =
            new LinkedHashMap<>();
    private final Map<String, List<String>> rpcSourcesByTarget =
            new LinkedHashMap<>();
    private final Map<String, List<FieldWrite>> fieldWritersByField =
            new LinkedHashMap<>();
    private final Map<String, List<ConstructorCallsite>> constructorCallersByCallee =
            new LinkedHashMap<>();
    private final Map<String, List<MethodCallsite>> methodCallersByCallee =
            new LinkedHashMap<>();
    private final Map<String, Set<String>> relevantFieldEffectsByMethod =
            new LinkedHashMap<>();
    private final Map<String, Set<String>> relevantByMethod = new LinkedHashMap<>();
    private final Map<String, Set<String>> relevantProjectionSuffixesByBase =
            new LinkedHashMap<>();
    private final Set<String> dirtyMethods = new LinkedHashSet<>();
    private final Map<String, List<StaticEdge>>
            projectableEdgesByEndpoint = new LinkedHashMap<>();
    private final Map<String, StaticEdge> dirtyProjectedEdges =
            new LinkedHashMap<>();
    private final Set<String> selectedMethods = new MethodWorkSet();
    private final Map<String, StaticEdge> emittedEdgeRows =
            new LinkedHashMap<>();
    private final Set<String> expandedDemands = new LinkedHashSet<>();
    private int discoveredExceptionSeedCount;
    private final Map<String, Boolean> receiverProjectionWriteSummary =
            new LinkedHashMap<>();
    /**
     * One call signature has at most one closed-world, side-effect-free
     * structural field accessor.  Negative resolutions are cached as null;
     * {@link Map#containsKey(Object)} distinguishes them from a cache miss.
     */
    private final Map<String, StructuralFieldAccessor>
            structuralFieldAccessors = new LinkedHashMap<>();
    private final Map<String, Set<String>> projectionAliasCache =
            new LinkedHashMap<>();
    private final Map<String, List<ExceptionGuard>> requiredPathGuardsByFact =
            new LinkedHashMap<>();
    private final RuntimeDispatchEvidence runtimeDispatchEvidence;
    private final Set<String> runtimeRecursiveMethods =
            new LinkedHashSet<>();
    private final List<StaticEdge> edges = new ArrayList<>();
    private boolean globalStaticIndexBuilt;
    private int edgeCounter;

    SeedBackwardStaticAnalyzer(CausynthTargetContext target) {
        this.target = target;
        this.maxMethods = positiveSystemProperty(
                "causynth.static.max.methods", DEFAULT_MAX_METHODS);
        this.maxEdges = positiveSystemProperty(
                "causynth.static.max.edges", DEFAULT_MAX_EDGES);
        try {
            this.runtimeDispatchEvidence =
                    RuntimeDispatchEvidence.fromConfiguration();
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load runtime dispatch evidence", exception);
        }
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            classesByName.put(sootClass.getName(), sootClass);
            for (SootMethod method : sootClass.getMethods()) {
                if (method.isConcrete()) {
                    methodsBySignature.put(method.getSignature(), method);
                    concreteMethodsBySubSignature
                            .computeIfAbsent(method.getSubSignature(),
                                    ignored -> new ArrayList<>())
                            .add(method);
                }
            }
        }
        buildRpcMappings();
    }

    private static int positiveSystemProperty(String property, int fallback) {
        Integer value = Integer.getInteger(property);
        return value != null && value > 0 ? value : fallback;
    }

    private void buildRpcMappings() {
        for (SootClass protocolClass : classesByName.values()) {
            String className = protocolClass.getName();
            if (!protocolClass.isInterface()
                    || !(className.contains("Protocol")
                    || className.contains("protocolPB")
                    || className.endsWith("PB"))) {
                continue;
            }
            for (SootMethod protocolMethod : protocolClass.getMethods()) {
                if (protocolMethod.isConcrete()
                        || "<init>".equals(protocolMethod.getName())
                        || "<clinit>".equals(protocolMethod.getName())) {
                    continue;
                }
                List<SootMethod> concreteMethods = concreteMethodsBySubSignature
                        .get(protocolMethod.getSubSignature());
                if (concreteMethods == null) {
                    continue;
                }
                for (SootMethod concreteMethod : concreteMethods) {
                    SootClass concreteClass = concreteMethod.getDeclaringClass();
                    if (concreteMethod.getSignature().equals(protocolMethod.getSignature())
                            || !concreteClass.isApplicationClass()
                            || !classImplementsOrExtends(concreteClass,
                            protocolClass.getName())) {
                        continue;
                    }
                    addRpcMapping(protocolMethod, concreteMethod);
                }
            }
        }
    }

    private void addRpcMapping(SootMethod source, SootMethod targetMethod) {
        String sourceSignature = source.getSignature();
        String targetSignature = targetMethod.getSignature();
        List<String> targets = rpcTargetsBySource.computeIfAbsent(
                sourceSignature, ignored -> new ArrayList<>());
        if (targets.contains(targetSignature)) {
            return;
        }
        targets.add(targetSignature);
        rpcSourcesByTarget.computeIfAbsent(targetSignature,
                ignored -> new ArrayList<>()).add(sourceSignature);
    }

    private boolean classImplementsOrExtends(SootClass candidate, String targetClassName) {
        return candidate != null && resolveInHierarchy(candidate,
                sootClass -> sootClass.getName().equals(targetClassName)
                        ? Boolean.TRUE : null) != null;
    }

    StaticProgram analyze() throws IOException {
        StaticProgram result = new StaticProgram();
        result.targetResolved.put("schemaVersion", 2);
        result.targetResolved.put("kind", "TARGET_ATTESTATION");
        result.targetResolved.put("targetId",
                target.exceptionTargetSite.id);
        result.targetResolved.put("method",
                target.exceptionTargetSite.methodSignature);
        result.targetResolved.put("exception", target.seedException);
        result.targetResolved.put("constructionOrdinal",
                target.exceptionTargetSite.exceptionConstructionOrdinal);
        result.targetResolved.put("analysisScope", target.analysisScope);
        loadClass(target.exceptionTargetSite.className);
        initializeExceptionSeedAnchors();
        runWorklist();
        if (discoveredExceptionSeedCount != 1) {
            throw new IllegalStateException("Annotated exception target did "
                    + "not resolve to exactly one Jimple throw: "
                    + target.exceptionTargetSite.stableIdentity()
                    + "; matches=" + discoveredExceptionSeedCount);
        }

        for (StaticEdge edge : edges) {
            result.edges.add(edge.row);
        }
        result.traceMethods.addAll(selectedMethods);
        Collections.sort(result.traceMethods);
        return result;
    }

    private void loadClass(String className) {
        SootClass sootClass = classesByName.get(className);
        if (sootClass != null) {
            for (SootMethod method : sootClass.getMethods()) {
                loadMethod(method);
            }
        }
        LOG.info("Loaded {} seed-candidate methods", factsByMethod.size());
    }

    private boolean loadMethod(SootMethod method) {
        if (method == null || !method.isConcrete()
                || factsByMethod.containsKey(method.getSignature())) {
            return false;
        }
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException exception) {
            return false;
        }
        List<Fact> facts = new ArrayList<>();
        int index = 0;
        for (Unit unit : body.getUnits()) {
            Fact fact = new Fact(method.getSignature(), index++, unit);
            facts.add(fact);
        }
        factsByMethod.put(method.getSignature(), facts);
        methodsBySignature.put(method.getSignature(), method);
        return true;
    }

    private void initializeExceptionSeedAnchors() {
        for (Map.Entry<String, List<Fact>> entry : factsByMethod.entrySet()) {
            String method = entry.getKey();
            if (!target.exceptionTargetSite.methodSignature.equals(method)) {
                continue;
            }
            List<Fact> facts = entry.getValue();
            for (int throwIndex = 0; throwIndex < facts.size(); throwIndex++) {
                Fact throwFact = facts.get(throwIndex);
                ExceptionConstruction construction =
                        annotatedExceptionConstruction(facts, throwIndex);
                if (construction == null) {
                    continue;
                }

                String exceptionNode = factNode(throwFact) + "#exception:"
                        + target.seedException;
                Set<String> methodRelevant = relevant(method);
                ThrowStmt throwStmt = (ThrowStmt) throwFact.unit;
                String thrownValue = canonical(method, throwStmt.getOp().toString());
                if (!ignoreNode(thrownValue)) {
                    methodRelevant.add(thrownValue);
                    addEdge("seed_exception_throw", thrownValue, exceptionNode,
                            method, throwFact,
                            "direct throw at annotated exception target");
                }

                for (String actual : construction.actuals) {
                    String node = canonical(method, actual);
                    if (ignoreNode(node)) {
                        continue;
                    }
                    methodRelevant.add(node);
                    addEdge("exception_payload_argument", node, exceptionNode,
                            method, construction.fact,
                            "exception constructor payload contributes to thrown value");
                }

                for (ExceptionGuard guard : targetPathBranches(method,
                        throwFact)) {
                    for (String use : causalGuardUses(guard.fact)) {
                        String node = canonical(method, use);
                        if (ignoreNode(node)) {
                            continue;
                        }
                        methodRelevant.add(node);
                        addEdge("exception_guard", node, exceptionNode,
                                method, guard.fact,
                                "dominating branch requires Jimple outcome "
                                        + guard.requiredOutcome
                                        + " to reach target throw");
                        StaticEdge edge = emittedEdgeRows.get(
                                edgeKey("exception_guard", node,
                                        exceptionNode, method,
                                        guard.fact));
                        if (edge != null) {
                            ControlDependenceEdgeSupport
                                    .annotatePathGuard(edge.row, method,
                                            guard.fact.unitIndex,
                                            throwFact.unitIndex,
                                            throwFact.unitText,
                                            guard.requiredOutcome,
                                            guard.reachingSuccessorIndices,
                                            node, exceptionNode);
                            guard.branchShape.annotate(edge.row);
                        }
                    }
                }

                selectedMethods.add(method);
                discoveredExceptionSeedCount++;
            }
        }
        LOG.info("Discovered {} direct throw sites for {} in {} methods",
                discoveredExceptionSeedCount, target.seedException,
                discoveredExceptionSeedCount == 0 ? 0 : 1);
    }

    private ExceptionConstruction annotatedExceptionConstruction(
            List<Fact> facts, int throwIndex) {
        Fact fact = facts.get(throwIndex);
        if (!(fact.unit instanceof ThrowStmt)) {
            return null;
        }
        ThrowStmt stmt = (ThrowStmt) fact.unit;
        ExceptionConstruction construction = findExceptionConstruction(facts,
                throwIndex, stmt.getOp().toString());
        if (construction == null) {
            return null;
        }
        int ordinal = 0;
        for (Fact candidate : facts) {
            MethodSig invoked = parseMethodSig(candidate.invoke);
            if (invoked == null || !"<init>".equals(invoked.name)
                    || !target.seedException.equals(invoked.owner)) {
                continue;
            }
            if (candidate == construction.fact) {
                if (ordinal != target.exceptionTargetSite
                        .exceptionConstructionOrdinal) {
                    return null;
                }
                int annotatedLine = target.exceptionTargetSite.sourceLine;
                if (annotatedLine > 0 && construction.fact.line > 0
                        && annotatedLine != construction.fact.line
                        && annotatedLine != fact.line) {
                    return null;
                }
                return construction;
            }
            ordinal++;
        }
        return null;
    }

    private ExceptionConstruction findExceptionConstruction(List<Fact> facts,
                                                            int throwIndex,
                                                            String thrownValue) {
        Set<String> work = new LinkedHashSet<>();
        String initial = localName(thrownValue);
        if (initial != null) {
            work.add(initial);
        }
        for (int i = throwIndex - 1; i >= 0 && !work.isEmpty(); i--) {
            Fact fact = facts.get(i);
            MethodSig invoked = parseMethodSig(fact.invoke);
            String receiver = invokeBaseLocal(fact.unitText);
            if (invoked != null && "<init>".equals(invoked.name)
                    && exceptionTypeMatches(invoked.owner)
                    && receiver != null && work.contains(receiver)) {
                return new ExceptionConstruction(fact,
                        actualInvokeArgs(fact.unitText));
            }
            Set<String> defs = localNames(fact.defs);
            if (!intersectsLocal(work, defs)) {
                continue;
            }
            work.addAll(localNames(nonInvokeUses(fact)));
            work.addAll(localNames(actualInvokeArgs(fact.unitText)));
        }
        return null;
    }

    private List<String> causalGuardUses(Fact guard) {
        List<String> values = new ArrayList<>();
        for (String use : localValueUses(guard)) {
            if (localName(use) != null || isFieldAccessValue(use)
                    || use.startsWith("@parameter")) {
                values.add(use);
            }
        }
        return values;
    }

    /**
     * Returns every dominating branch for which only a proper subset of
     * successors can reach {@code targetFact}.  Consequently, each result
     * is a path condition that must take one particular successor for the
     * target statement to execute.
     *
     * <p>This is intentionally usable for more than the initial throw.
     * Jimple commonly lowers a boolean expression to guarded constant
     * assignments.  Following only local def-use edges would then stop at
     * the constants and lose the source condition.  The normal worklist
     * therefore reuses this query for relevant definitions as well.</p>
     */
    private List<ExceptionGuard> controllingGuards(String method,
                                                   Fact targetFact) {
        String cacheKey = method + "\n" + targetFact.unitIndex;
        List<ExceptionGuard> cached = requiredPathGuardsByFact.get(cacheKey);
        if (cached != null) {
            return cached;
        }
        List<ExceptionGuard> result = branchGuards(method, targetFact,
                true);
        requiredPathGuardsByFact.put(cacheKey, result);
        return result;
    }

    /**
     * Returns every branch in the annotated exception method which lies on
     * at least one path to the exact throw.  This is intentionally broader
     * than control dependence: javac lowers {@code a || b} to two branches,
     * and both successors of the first branch can reach the throw even
     * though that branch is still one alternative target-path decision.
     */
    private List<ExceptionGuard> targetPathBranches(String method,
                                                    Fact targetFact) {
        return branchGuards(method, targetFact, false);
    }

    private List<ExceptionGuard> branchGuards(String method,
                                              Fact targetFact,
                                              boolean controllingOnly) {
        MethodControlFlow controlFlow = controlFlow(method);
        if (controlFlow == null || targetFact.unit == null) {
            return Collections.emptyList();
        }
        Set<Unit> dominators = Collections.emptySet();
        if (controllingOnly) {
            dominators = Collections.newSetFromMap(
                    new IdentityHashMap<Unit, Boolean>());
            try {
                dominators.addAll(controlFlow.dominators
                        .getDominators(targetFact.unit));
            } catch (RuntimeException ignored) {
                return Collections.emptyList();
            }
        }
        List<ExceptionGuard> guards = new ArrayList<>();
        for (Fact candidate : factsByMethod.getOrDefault(method,
                Collections.emptyList())) {
            if (!candidate.isBranch
                    || controllingOnly
                    && !dominators.contains(candidate.unit)) {
                continue;
            }
            CausynthBranchShape branchShape =
                    CausynthBranchShape.from(controlFlow.body,
                            candidate.unit);
            if (branchShape == null
                    || branchShape.successorCount() < 2) {
                continue;
            }
            List<Unit> successors = branchShape.successors;
            int reachingSuccessors = 0;
            List<Integer> reachingIndices = new ArrayList<>();
            for (int successorIndex = 0;
                successorIndex < successors.size(); successorIndex++) {
                if (canReachWithoutRevisiting(controlFlow.graph,
                        successors.get(successorIndex), targetFact.unit,
                        candidate.unit)) {
                    reachingSuccessors++;
                    reachingIndices.add(successorIndex);
                }
            }
            boolean relevant = reachingSuccessors > 0
                    && (!controllingOnly
                    || reachingSuccessors < successors.size());
            if (relevant) {
                Fact guard = controlFlow.factsByUnit.get(candidate.unit);
                if (guard != null) {
                    Boolean requiredOutcome = null;
                    if (candidate.unit instanceof IfStmt) {
                        IfStmt ifStmt = (IfStmt) candidate.unit;
                        boolean takenReaches = canReachWithoutRevisiting(
                                controlFlow.graph, ifStmt.getTarget(),
                                targetFact.unit,
                                candidate.unit);
                        Unit fallThrough = controlFlow.body.getUnits()
                                .getSuccOf(candidate.unit);
                        boolean fallThroughReaches = fallThrough != null
                                && canReachWithoutRevisiting(
                                controlFlow.graph,
                                fallThrough, targetFact.unit,
                                candidate.unit);
                        if (takenReaches != fallThroughReaches) {
                            requiredOutcome = takenReaches;
                        }
                    }
                    guards.add(new ExceptionGuard(guard, requiredOutcome,
                            reachingIndices,
                            branchShape));
                }
            }
        }
        guards.sort(Comparator.comparingInt(guard -> guard.fact.unitIndex));
        return Collections.unmodifiableList(guards);
    }

    private MethodControlFlow controlFlow(String method) {
        if (controlFlowByMethod.containsKey(method)) {
            return controlFlowByMethod.get(method);
        }
        SootMethod sootMethod = methodsBySignature.get(method);
        if (sootMethod == null) {
            return null;
        }
        try {
            Body body = sootMethod.retrieveActiveBody();
            UnitGraph graph = new BriefUnitGraph(body);
            Map<Unit, Fact> factsByUnit = new IdentityHashMap<>();
            for (Fact fact : factsByMethod.getOrDefault(method,
                    Collections.emptyList())) {
                factsByUnit.put(fact.unit, fact);
            }
            MethodControlFlow controlFlow = new MethodControlFlow(
                    body, graph, factsByUnit);
            controlFlowByMethod.put(method, controlFlow);
            return controlFlow;
        } catch (RuntimeException ignored) {
            return null;
        }
    }

    /**
     * Tests reachability within the current dynamic occurrence of a
     * candidate branch.  A plain graph reachability query is insufficient
     * inside a loop: the successor which skips a mutation in this
     * iteration can revisit the same predicate on a later iteration and
     * then reach the mutation, making both successors appear causal.
     * Excluding the candidate after leaving it preserves the per-
     * occurrence branch semantics consumed by the concolic scheduler.
     */
    private boolean canReachWithoutRevisiting(UnitGraph graph, Unit start,
                                               Unit targetUnit,
                                               Unit candidateBranch) {
        Set<Unit> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Deque<Unit> work = new ArrayDeque<>();
        work.add(start);
        while (!work.isEmpty()) {
            Unit current = work.removeFirst();
            if (current == targetUnit) {
                return true;
            }
            if (current == candidateBranch || !seen.add(current)) {
                continue;
            }
            work.addAll(graph.getSuccsOf(current));
        }
        return false;
    }

    private boolean exceptionTypeMatches(String candidateType) {
        if (candidateType == null) {
            return false;
        }
        String candidate = candidateType.trim();
        String configured = target.seedException.trim();
        if (configured.equals(candidate)
                || (!configured.contains(".")
                && configured.equals(simpleClassName(candidate)))) {
            return true;
        }
        SootClass current = classesByName.get(candidate);
        Set<String> seen = new LinkedHashSet<>();
        while (current != null && seen.add(current.getName())) {
            if (configured.equals(current.getName())
                    || (!configured.contains(".")
                    && configured.equals(simpleClassName(current.getName())))) {
                return true;
            }
            try {
                current = current.hasSuperclass() ? current.getSuperclass() : null;
            } catch (RuntimeException ignored) {
                return false;
            }
        }
        return false;
    }

    private String simpleClassName(String className) {
        if (className == null) {
            return "";
        }
        int dot = className.lastIndexOf('.');
        return dot < 0 ? className : className.substring(dot + 1);
    }

    private boolean intersectsLocal(Set<String> left, Set<String> right) {
        for (String value : right) {
            if (left.contains(value)) {
                return true;
            }
        }
        return false;
    }

    private Set<String> localNames(Collection<String> values) {
        Set<String> locals = new LinkedHashSet<>();
        for (String value : values) {
            String local = localName(value);
            if (local != null) {
                locals.add(local);
            }
        }
        return locals;
    }

    private String localName(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        if (LOCAL_NAME_PATTERN.matcher(trimmed).matches()) {
            return trimmed;
        }
        Matcher cast = CAST_LOCAL_PATTERN.matcher(trimmed);
        if (trimmed.startsWith("(") && cast.find()) {
            return cast.group(1);
        }
        return null;
    }

    private String invokeBaseLocal(String unitText) {
        Matcher matcher = INVOKE_BASE_PATTERN.matcher(unitText);
        if (matcher.find()) {
            return matcher.group(1);
        }
        return null;
    }

    private void runWorklist() {
        // Monotone fixed point: selecting a method or adding one relevant
        // cell queues that method once. Adding a projected cell queues only
        // previously emitted base edges with a matching endpoint prefix.
        while ((!dirtyMethods.isEmpty() || !dirtyProjectedEdges.isEmpty())
                && edges.size() < maxEdges) {
            while (!dirtyMethods.isEmpty() && edges.size() < maxEdges) {
                String method = dirtyMethods.iterator().next();
                dirtyMethods.remove(method);
                if (!selectedMethods.contains(method)) {
                    continue;
                }
                processMethod(method);
                expandRpcCallers(method);
                expandDispatchCallers(method);
                expandFieldWriters(method);
                expandConstructorCallers(method);
                expandMethodCallers(method);
            }
            while (!dirtyProjectedEdges.isEmpty()
                    && edges.size() < maxEdges) {
                String edgeId = dirtyProjectedEdges.keySet().iterator().next();
                StaticEdge edge =
                        dirtyProjectedEdges.remove(edgeId);
                propagateProjectedEdge(edge);
            }
        }
    }

    private void processMethod(String method) {
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null) {
            return;
        }
        Set<String> relevant = relevant(method);
        MethodSig methodSig = parseMethodSig(method);
        for (Fact fact : facts) {
            List<String> defs = canonicalList(method, fact.defs);
            List<String> uses = canonicalList(method, localValueUses(fact));
            if (fact.isReturn) {
                defs.add(method + ".return");
            }
            if (fact.unitText.contains("@parameter") && methodSig != null) {
                uses.addAll(parameterNodesFromUnit(methodSig, fact.unitText));
            }

            boolean defExactHit = exactIntersects(relevant, defs);
            boolean defProjectionHit = projectionIntersects(relevant, defs);
            if (!defExactHit && defProjectionHit) {
                promoteArrayContainerForProjectedElementRead(
                        method, fact, relevant);
                promoteTypedCastOperandForProjectedFieldDemand(
                        method, fact, relevant);
            }
            boolean defHit = defExactHit || defProjectionHit;
            boolean useExactHit = exactIntersects(relevant, uses);
            boolean useProjectionHit = projectionIntersects(relevant, uses);
            boolean useHit = useExactHit || useProjectionHit;
            if (defProjectionHit && uses.isEmpty()
                    && fact.unit instanceof AssignStmt) {
                String allocated = ((AssignStmt) fact.unit).getRightOp()
                        .toString();
                if (allocated.startsWith("new ")) {
                    for (String def : defs) {
                        addEdge("local_def_use", allocated, def, method, fact,
                                "fresh allocation defines projected receiver");
                    }
                }
            }
            if (defHit || useHit) {
                for (String def : defs) {
                    for (String use : uses) {
                        if (ignoreNode(def) || ignoreNode(use)) {
                            continue;
                        }
                        addEdge("local_def_use", use, def, method, fact,
                                "Jimple use/field/argument flows to def");
                    }
                }
                if (defExactHit) {
                    for (String use : uses) {
                        relevant.add(use);
                    }
                }
                if (useHit) {
                    for (String def : defs) {
                        relevant.add(def);
                    }
                }
            }

            if (defExactHit) {
                processRequiredPathGuards(method, fact, defs,
                        relevant);
            }

            if (fact.isBranch && useExactHit) {
                for (String use : uses) {
                    addEdge("guard_dependency", use, factNode(fact),
                            method, fact, "branch consumes relevant value");
                }
            }
            if (fact.isThrow && useExactHit) {
                for (String use : uses) {
                    addEdge("throw_dependency", use, factNode(fact),
                            method, fact, "throw consumes relevant value");
                }
            }
            processFieldReads(method, fact, defs, relevant);
            processFieldWrites(method, facts, fact, relevant);
            processInvoke(method, fact, defs, relevant);
        }
    }

    /**
     * A field demanded from an array element also demands the array value
     * that selected that element.  Ordinary field-path propagation cannot
     * express this transition: {@code Key[]} is a container, not an
     * object on which {@code keyId} (or any other element field) is
     * declared.  Keep the exact array-load edge and promote only its base
     * to an ordinary relevant value.  The subsequent backward rounds can
     * then close the base through an accessor return, method argument, or
     * declared array field without inventing an invalid
     * {@code array#field:keyId} cell.
     */
    private void promoteArrayContainerForProjectedElementRead(
            String method, Fact fact, Set<String> relevant) {
        if (!(fact.unit instanceof AssignStmt)) {
            return;
        }
        Value right = ((AssignStmt) fact.unit).getRightOp();
        if (!(right instanceof ArrayRef)) {
            return;
        }
        String base = canonical(method,
                ((ArrayRef) right).getBase().toString());
        if (!ignoreNode(base)) {
            relevant.add(base);
        }
    }

    /**
     * A checkcast gives an otherwise untyped reference the declared type
     * needed to interpret a demanded field path.  Promote only the cast
     * operand as an exact value: this lets an upstream modeled operation such
     * as {@code Map.get} close over its receiver and arguments without ever
     * inventing a globally valid {@code java.lang.Object#field:*} projection.
     */
    private void promoteTypedCastOperandForProjectedFieldDemand(
            String method, Fact fact, Set<String> relevant) {
        if (!(fact.unit instanceof AssignStmt)) {
            return;
        }
        Value right = ((AssignStmt) fact.unit).getRightOp();
        if (!(right instanceof CastExpr)
                || !(((CastExpr) right).getType() instanceof soot.RefType)
                || !(((CastExpr) right).getOp() instanceof Local)) {
            return;
        }
        String operand = canonical(method,
                ((CastExpr) right).getOp().toString());
        if (!ignoreNode(operand)) {
            relevant.add(operand);
        }
    }

    /**
     * Adds intraprocedural control dependencies for a statement that
     * defines an exactly relevant value.  This keeps the old def-use
     * worklist intact while allowing it to cross Jimple's branch-based
     * lowering of expressions such as {@code Time.now() > expiryDate}.
     */
    private void processRequiredPathGuards(String method, Fact targetFact,
                                           List<String> defs,
                                           Set<String> relevant) {
        if (targetFact.isBranch) {
            return;
        }
        List<String> relevantDefs = new ArrayList<>();
        for (String def : defs) {
            if (relevant.contains(def) && !ignoreNode(def)) {
                relevantDefs.add(def);
            }
        }
        if (relevantDefs.isEmpty()) {
            return;
        }

        for (ExceptionGuard guard : controllingGuards(method, targetFact)) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(method, use);
                if (ignoreNode(guardNode)) {
                    continue;
                }
                for (String def : relevantDefs) {
                    addEdge(
                            ControlDependenceEdgeSupport.PATH_GUARD_KIND,
                            guardNode, def, method, guard.fact,
                            "dominating branch requires Jimple outcome "
                                    + guard.requiredOutcome
                                    + " to reach relevant definition at u"
                                    + targetFact.unitIndex);
                    StaticEdge edge = emittedEdgeRows.get(edgeKey(
                            ControlDependenceEdgeSupport.PATH_GUARD_KIND,
                            guardNode, def, method, guard.fact));
                    if (edge != null) {
                        ControlDependenceEdgeSupport.annotatePathGuard(
                                edge.row, method, guard.fact.unitIndex,
                                targetFact.unitIndex,
                                targetFact.unitText,
                                guard.requiredOutcome,
                                guard.reachingSuccessorIndices,
                                guardNode, def);
                        guard.branchShape.annotate(edge.row);
                    }
                }
                relevant.add(guardNode);
            }
        }
    }

    private void processFieldReads(String method, Fact fact,
                                   List<String> defs, Set<String> relevant) {
        for (String field : fact.fieldUses) {
            String fieldNode = canonical(method, field);
            if (ignoreNode(fieldNode)) {
                continue;
            }
            boolean defExactHit = exactIntersects(relevant, defs);
            boolean defProjectionHit = projectionIntersects(relevant, defs);
            boolean defHit = defExactHit || defProjectionHit;
            if (!defHit) {
                continue;
            }
            for (String def : defs) {
                if (ignoreNode(def)) {
                    continue;
                }
                addEdge("field_read", fieldNode, def, method, fact,
                        "field value flows to local/return");
                annotateDirectDeclaredFieldEdge("field_read", fieldNode,
                        def, method, fact, field);
            }
            if (defExactHit && canOpenFieldFromPlainValues(defs)) {
                relevant.add(fieldNode);
            }
        }
        for (InstanceFieldAccess access : fact.instanceFieldUses) {
            String fieldName = fieldNameFromSignature(access.field);
            String receiverField = fieldProjection(canonical(method, access.base), fieldName);
            if (ignoreNode(receiverField)) {
                continue;
            }
            boolean defExactHit = exactIntersects(relevant, defs);
            boolean defProjectionHit = projectionIntersects(relevant, defs);
            boolean defHit = defExactHit || defProjectionHit;
            if (!defHit) {
                continue;
            }
            for (String def : defs) {
                if (ignoreNode(def)) {
                    continue;
                }
                addEdge("instance_field_read", receiverField, def, method,
                        fact, "receiver field value flows to local/return");
                annotateDirectDeclaredFieldEdge("instance_field_read",
                        receiverField, def, method, fact, access.field);
            }
            if (defExactHit && canOpenFieldFromPlainValues(defs)) {
                relevant.add(receiverField);
            }
        }
    }

    private void processFieldWrites(String method, List<Fact> facts, Fact fact,
                                    Set<String> relevant) {
        Set<String> affectedRelevantHeapCells = new LinkedHashSet<>();
        for (String field : fact.fieldDefs) {
            String fieldNode = canonical(method, field);
            if (relevant.contains(fieldNode)) {
                affectedRelevantHeapCells.add(fieldNode);
            }
            processFieldWrite(method, fact, relevant, field,
                    fieldWriteSources(method, fact, field), "field_write",
                    "assignment writes relevant field");
        }
        for (InstanceFieldAccess access : fact.instanceFieldDefs) {
            String fieldName = fieldNameFromSignature(access.field);
            String receiverField = fieldProjection(canonical(method, access.base), fieldName);
            if (ignoreNode(receiverField)) {
                continue;
            }
            List<String> sources = fieldWriteSources(method, fact, access.field);
            if (sources.isEmpty()) {
                sources = Collections.singletonList(factNode(fact));
            }
            String classField = canonical(method, access.field);
            boolean receiverExactHit = relevant.contains(receiverField);
            boolean receiverProjectionHit = containsProjection(relevant, receiverField);
            boolean receiverHit = receiverExactHit || receiverProjectionHit;
            boolean classFieldHit = relevant.contains(classField);
            if (receiverHit || classFieldHit) {
                if (receiverHit) {
                    affectedRelevantHeapCells.add(receiverField);
                }
                affectedRelevantHeapCells.add(classField);
                for (String source : sources) {
                    if (ignoreNode(source)) {
                        continue;
                    }
                    addEdge("instance_field_write", source, receiverField,
                            method, fact, "assignment writes receiver field");
                    // A receiver-sensitive write also updates the declared
                    // class field.  Preserve both views: the receiver
                    // projection lets runtime match object identity, while
                    // the class-field node connects possible writers and
                    // readers across threads before identities are known.
                    addEdge("field_write", source, classField, method, fact,
                            "receiver assignment writes declared field");
                    relevant.add(classField);
                    if ((receiverExactHit || classFieldHit)
                            && canOpenFieldFromPlainValue(source)) {
                        relevant.add(source);
                    }
                }
            }
        }
        for (String mutatedField : fieldsMutatedByInvoke(facts, fact.unitIndex)) {
            String mutatedFieldNode = canonical(method, mutatedField);
            boolean mutationAffectsRelevantState =
                    relevant.contains(mutatedFieldNode);
            processFieldWrite(method, fact, relevant, mutatedField,
                    fieldMutationSources(method, fact, mutatedField),
                    "field_mutation",
                    "mutator call updates object stored in relevant field");
            if (mutationAffectsRelevantState) {
                affectedRelevantHeapCells.add(mutatedFieldNode);
            }
        }
        for (String affectedCell : affectedRelevantHeapCells) {
            processHeapMutationPathGuards(method, fact,
                    affectedCell, relevant);
        }
    }

    /**
     * A heap write may have no exactly relevant Jimple definition local, so the ordinary
     * {@link #processRequiredPathGuards(String, Fact, List, Set)} path
     * cannot reliably attach the branches that make the write execute.
     * Treat the affected heap cell as the definition for control-dependence
     * purposes. This covers ordinary field assignments and collection
     * updates, including an {@code Iterator.remove()} guarded by a predicate.
     */
    private void processHeapMutationPathGuards(
            String method, Fact mutation, String mutatedCell,
            Set<String> relevant) {
        if (ignoreNode(mutatedCell)) {
            return;
        }
        for (ExceptionGuard guard : controllingGuards(method, mutation)) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(method, use);
                if (ignoreNode(guardNode)) {
                    continue;
                }
                addHeapMutationPathGuardEdge(guardNode,
                        mutatedCell, method, guard, mutation);
                relevant.add(guardNode);
            }
        }
    }

    private void addHeapMutationPathGuardEdge(
            String guardNode, String mutatedCell, String method,
            ExceptionGuard guard, Fact mutation) {
        String evidence = "dominating branch requires Jimple outcome "
                + guard.requiredOutcome + " to reach heap mutation at u"
                + mutation.unitIndex;
        addEdge("heap_mutation_path_guard", guardNode,
                mutatedCell, method, guard.fact, evidence);
        String key = edgeKey("heap_mutation_path_guard", guardNode,
                mutatedCell, method, guard.fact);
        StaticEdge edge = emittedEdgeRows.get(key);
        if (edge == null) {
            return;
        }
        ControlDependenceEdgeSupport.annotateGuardedMutation(
                edge.row, method, guard.fact.unitIndex, mutation.unitIndex,
                guard.requiredOutcome, guard.reachingSuccessorIndices);
        guard.branchShape.annotate(edge.row);
    }

    private void processFieldWrite(String method, Fact fact,
                                   Set<String> relevant, String field,
                                   List<String> sources, String kind,
                                   String evidence) {
        String fieldNode = canonical(method, field);
        if (ignoreNode(fieldNode)) {
            return;
        }
        boolean fieldHit = relevant.contains(fieldNode);
        if (!fieldHit) {
            return;
        }
        if (sources.isEmpty()) {
            sources = Collections.singletonList(factNode(fact));
        }
        for (String source : sources) {
            if (ignoreNode(source)) {
                continue;
            }
            addEdge(kind, source, fieldNode, method, fact, evidence);
            if (fieldHit && canOpenFieldFromPlainValue(source)) {
                relevant.add(source);
            }
        }
    }

    private void expandFieldWriters(String method) {
        List<String> fields = relevant(method).stream()
                .filter(this::isApplicationField)
                .collect(Collectors.toList());
        if (fields.isEmpty()) {
            return;
        }
        buildGlobalStaticIndex();
        for (String field : fields) {
            if (!expandOnce("FIELD_WRITERS", field)) {
                continue;
            }
            List<FieldWrite> writers = fieldWritersByField.get(field);
            if (writers == null || writers.isEmpty()) {
                continue;
            }
            int count = 0;
            for (FieldWrite writer : writers) {
                if (count++ >= MAX_FIELD_WRITERS_PER_FIELD
                        || selectedMethods.size() >= maxMethods
                        || edges.size() >= maxEdges) {
                    break;
                }
                SootMethod writerMethod = methodsBySignature.get(writer.method);
                if (writerMethod != null) {
                    loadMethod(writerMethod);
                }
                Set<String> writerRelevant = relevant(writer.method);
                writerRelevant.add(writer.field);
                relevantFieldEffectsByMethod
                        .computeIfAbsent(writer.method,
                                ignored -> new LinkedHashSet<>())
                        .add(writer.field);
                selectedMethods.add(writer.method);
                List<String> sources = writer.sources.isEmpty()
                        ? Collections.singletonList(factNode(writer.fact))
                        : writer.sources;
                for (String source : sources) {
                    if (ignoreNode(source)) {
                        continue;
                    }
                    addEdge(writer.kind, source, writer.field, writer.method,
                            writer.fact, writer.evidence);
                    if (canOpenFieldFromPlainValue(source)) {
                        writerRelevant.add(source);
                    }
                }
            }
        }
    }

    private void expandConstructorCallers(String method) {
        List<ConstructorParam> params = relevant(method).stream()
                .map(this::constructorParam)
                .filter(param -> param != null)
                .collect(Collectors.toList());
        String thisNode = methodThisNode(method);
        Set<String> thisProjectionSuffixes =
                projectionSuffixesForBase(thisNode);
        if (params.isEmpty() && thisProjectionSuffixes.isEmpty()) {
            return;
        }
        buildGlobalStaticIndex();
        Set<String> constructorsToExpand = new LinkedHashSet<>();
        for (ConstructorParam param : params) {
            constructorsToExpand.add(param.constructor);
        }
        if (thisNode != null && !thisProjectionSuffixes.isEmpty()) {
            constructorsToExpand.add(method);
        }
        for (String constructor : constructorsToExpand) {
            List<ConstructorCallsite> callsites = constructorCallersByCallee
                    .get(constructor);
            if (callsites == null || callsites.isEmpty()) {
                continue;
            }
            if (constructor.equals(method)) {
                for (ConstructorCallsite callsite : callsites) {
                    expandConstructorReceiverFields(method, thisNode,
                            thisProjectionSuffixes, callsite);
                }
            }
        }
        for (ConstructorParam param : params) {
            if (!expandOnce("CONSTRUCTOR_PARAM", param.constructor,
                    param.index)) {
                continue;
            }
            List<ConstructorCallsite> callsites = constructorCallersByCallee
                    .get(param.constructor);
            if (callsites == null || callsites.isEmpty()) {
                continue;
            }
            int count = 0;
            for (ConstructorCallsite callsite : callsites) {
                if (selectedMethods.size() >= maxMethods
                        || edges.size() >= maxEdges
                        || count++ >= MAX_CONSTRUCTOR_CALLERS_PER_PARAM) {
                    break;
                }
                if (param.index >= callsite.actuals.size()) {
                    continue;
                }
                String actual = callsite.actuals.get(param.index);
                if (ignoreNode(actual)) {
                    continue;
                }
                SootMethod callerMethod = methodsBySignature.get(callsite.method);
                if (callerMethod != null) {
                    loadMethod(callerMethod);
                }
                addEdge("constructor_caller_argument", actual, param.formal,
                        callsite.method, callsite.fact,
                        "constructor caller actual reaches relevant constructor formal");
                relevant(callsite.method).add(actual);
                selectedMethods.add(callsite.method);
            }
        }
    }

    private void expandMethodCallers(String method) {
        MethodSig callee = parseMethodSig(method);
        if (callee == null || "<init>".equals(callee.name)
                || "<clinit>".equals(callee.name)
                || !isApplicationClassName(callee.owner)) {
            return;
        }
        Set<String> calleeRelevant = relevant(method);
        String thisNode = methodThisNode(method);
        Set<String> thisProjectionSuffixes =
                projectionSuffixesForBase(thisNode);
        boolean thisRelevant = thisNode != null
                && (calleeRelevant.contains(thisNode)
                || !thisProjectionSuffixes.isEmpty());
        String returnNode = method + ".return";
        boolean returnRelevant = calleeRelevant.contains(returnNode)
                || containsProjection(calleeRelevant, returnNode);
        List<Integer> relevantParams = new ArrayList<>();
        for (int i = 0; i < callee.params.size(); i++) {
            String formal = formalParam(callee, i);
            if (calleeRelevant.contains(formal)
                    || containsProjection(calleeRelevant, formal)) {
                relevantParams.add(i);
            }
        }
        if (relevantParams.isEmpty() && !thisRelevant && !returnRelevant) {
            return;
        }

        buildGlobalStaticIndex();
        List<MethodCallsite> callsites = methodCallersByCallee.get(method);
        if (callsites == null || callsites.isEmpty()) {
            return;
        }

        int count = 0;
        for (MethodCallsite callsite : callsites) {
            if (count++ >= MAX_METHOD_CALLERS_PER_METHOD
                    || selectedMethods.size() >= maxMethods
                    || edges.size() >= maxEdges) {
                break;
            }
            SootMethod callerMethod = methodsBySignature.get(callsite.method);
            if (callerMethod != null) {
                loadMethod(callerMethod);
            }
            Set<String> callerRelevant = relevant(callsite.method);
            for (int index : relevantParams) {
                if (!expandOnce("METHOD_CALLER_PARAM", method, index,
                        callsite.method, callsite.fact.unitIndex)
                        || index >= callsite.actuals.size()) {
                    continue;
                }
                String actual = callsite.actuals.get(index);
                if (ignoreNode(actual)) {
                    addTypedLiteralCallerArgument(callee,
                            index, callsite);
                    if (isTypedLiteralArgument(callsite.fact, index,
                            callee.params.get(index))) {
                        selectedMethods.add(callsite.method);
                    }
                    continue;
                }
                addEdge("caller_argument", actual,
                        formalParam(callee, index), callsite.method, callsite.fact,
                        "method caller actual reaches relevant callee formal");
                callerRelevant.add(actual);
                selectedMethods.add(callsite.method);
            }
            addReceiverFieldEffectPathGuards(method,
                    callsite, callerRelevant);
            if (thisRelevant) {
                expandCallerReceiverFields(false, method, thisNode,
                        thisProjectionSuffixes, callsite);
            }
            if (returnRelevant && expandOnce("METHOD_CALLER_RETURN", method,
                    callsite.method, callsite.fact.unitIndex)) {
                expandCallerReturn("caller_return",
                        returnNode, callsite.defs, callsite.method,
                        callsite.fact, callerRelevant,
                        "method caller receives relevant callee return");
            }
        }
    }

    private void addTypedLiteralCallerArgument(MethodSig callee,
                                               int argumentIndex,
                                               MethodCallsite callsite) {
        Value literal = invokeArgument(callsite.fact, argumentIndex);
        if (!(literal instanceof Constant)
                || argumentIndex < 0
                || argumentIndex >= callee.params.size()) {
            return;
        }
        String formalType = callee.params.get(argumentIndex);
        String literalValue = typedLiteralValue(literal, formalType);
        if (literalValue.isEmpty()) {
            return;
        }
        String source = factNode(callsite.fact);
        String target = formalParam(callee, argumentIndex);
        addEdge("method_caller_literal_argument",
                source, target, callsite.method, callsite.fact,
                "exact callsite supplies a typed literal to relevant callee formal");
    }

    private boolean isTypedLiteralArgument(Fact fact, int argumentIndex,
                                           String formalType) {
        Value value = invokeArgument(fact, argumentIndex);
        return value instanceof Constant
                && !typedLiteralValue(value, formalType).isEmpty();
    }

    private Value invokeArgument(Fact fact, int argumentIndex) {
        if (fact == null || argumentIndex < 0
                || !(fact.unit instanceof Stmt)) {
            return null;
        }
        Stmt statement = (Stmt) fact.unit;
        if (!statement.containsInvokeExpr()
                || argumentIndex >= statement.getInvokeExpr()
                .getArgCount()) {
            return null;
        }
        return statement.getInvokeExpr().getArg(argumentIndex);
    }

    private String typedLiteralValue(Value literal, String formalType) {
        if (literal == null || formalType == null) {
            return "";
        }
        if ("boolean".equals(formalType)) {
            if (!(literal instanceof IntConstant)) {
                return "";
            }
            int value = ((IntConstant) literal).value;
            return value == 0 ? "false" : value == 1 ? "true" : "";
        }
        return literal instanceof Constant ? literal.toString() : "";
    }

    /**
     * A relevant field-writing call is a heap effect even when its data
     * argument is a constant.  Preserve the caller-side control
     * dependence on the exact effect site so a condition such as
     * shouldUpdateBlockKey can recursively enter the backward slice.
     */
    private void addReceiverFieldEffectPathGuards(
            String calleeMethod, MethodCallsite callsite,
            Set<String> callerRelevant) {
        Set<String> effectFields = relevantFieldEffectsByMethod.get(
                calleeMethod);
        if (effectFields == null || effectFields.isEmpty()) {
            return;
        }
        for (ExceptionGuard guard : controllingGuards(callsite.method,
                callsite.fact)) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(callsite.method, use);
                if (ignoreNode(guardNode)) {
                    continue;
                }
                for (String effectField : effectFields) {
                    if (!expandOnce("RECEIVER_EFFECT_GUARD", calleeMethod,
                            callsite.method, callsite.fact.unitIndex,
                            guard.fact.unitIndex, guardNode, effectField)) {
                        continue;
                    }
                    addReceiverFieldEffectPathGuardEdge(
                            guardNode, effectField, calleeMethod,
                            callsite, guard);
                }
                callerRelevant.add(guardNode);
                selectedMethods.add(callsite.method);
            }
        }
    }

    private void addReceiverFieldEffectPathGuardEdge(
            String guardNode, String effectField, String calleeMethod,
            MethodCallsite callsite, ExceptionGuard guard) {
        String kind = "receiver_field_effect_path_guard";
        addEdge(kind, guardNode, effectField,
                callsite.method, guard.fact,
                "dominating branch controls relevant receiver field effect at call u"
                        + callsite.fact.unitIndex);
        StaticEdge edge = emittedEdgeRows.get(edgeKey(kind,
                guardNode, effectField, callsite.method, guard.fact));
        if (edge == null) {
            return;
        }
        ControlDependenceEdgeSupport.annotateGuardedReceiverEffect(
                edge.row, callsite.method, guard.fact.unitIndex,
                callsite.fact.unitIndex, guard.requiredOutcome,
                guard.reachingSuccessorIndices, calleeMethod,
                effectField);
        guard.branchShape.annotate(edge.row);
    }

    private ConstructorParam constructorParam(String node) {
        if (node == null) {
            return null;
        }
        int marker = node.indexOf(">.param");
        if (marker < 0) {
            return null;
        }
        String constructor = node.substring(0, marker + 1);
        MethodSig sig = parseMethodSig(constructor);
        if (sig == null || !"<init>".equals(sig.name)
                || !isApplicationClassName(sig.owner)) {
            return null;
        }
        Matcher matcher = CONSTRUCTOR_PARAMETER_PATTERN.matcher(node);
        if (!matcher.find()) {
            return null;
        }
        int index = Integer.parseInt(matcher.group(1));
        if (index < 0 || index >= sig.params.size()) {
            return null;
        }
        return new ConstructorParam(constructor, index, formalParam(sig, index));
    }

    private void buildGlobalStaticIndex() {
        if (globalStaticIndexBuilt) {
            return;
        }
        globalStaticIndexBuilt = true;
        for (SootMethod method : methodsBySignature.values()) {
            if (!method.isConcrete()
                    || !method.getDeclaringClass().isApplicationClass()) {
                continue;
            }
            List<Fact> facts = factsByMethod.get(method.getSignature());
            if (facts == null) {
                facts = factsFromMethod(method);
            }
            if (facts.isEmpty()) {
                continue;
            }
            indexMethod(method.getSignature(), facts);
        }
        LOG.info("Indexed writers for {} application fields, callers for {} constructors, "
                        + "and callers for {} methods",
                fieldWritersByField.size(), constructorCallersByCallee.size(),
                methodCallersByCallee.size());
    }

    private List<Fact> factsFromMethod(SootMethod method) {
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException exception) {
            return Collections.emptyList();
        }
        List<Fact> facts = new ArrayList<>();
        int index = 0;
        for (Unit unit : body.getUnits()) {
            facts.add(new Fact(method.getSignature(), index++, unit));
        }
        return facts;
    }

    private void addIndexedFieldWrite(FieldWrite write) {
        if (!isApplicationField(write.field)) {
            return;
        }
        List<FieldWrite> writers = fieldWritersByField
                .computeIfAbsent(write.field, ignored -> new ArrayList<>());
        if (writers.size() < MAX_FIELD_WRITERS_PER_FIELD) {
            writers.add(write);
        }
    }

    private void addIndexedConstructorCallsite(ConstructorCallsite callsite) {
        MethodSig sig = parseMethodSig(callsite.constructor);
        if (sig == null || !isApplicationClassName(sig.owner)) {
            return;
        }
        constructorCallersByCallee
                .computeIfAbsent(callsite.constructor, ignored -> new ArrayList<>())
                .add(callsite);
    }

    private void addIndexedMethodCallsite(MethodCallsite callsite) {
        MethodSig sig = parseMethodSig(callsite.callee);
        if (sig == null || !isApplicationClassName(sig.owner)) {
            return;
        }
        List<MethodCallsite> callsites = methodCallersByCallee
                .computeIfAbsent(callsite.callee, ignored -> new ArrayList<>());
        if (callsites.size() < MAX_METHOD_CALLERS_PER_METHOD) {
            callsites.add(callsite);
        }
    }

    private void indexMethod(String method, List<Fact> facts) {
        for (Fact fact : facts) {
            for (String field : fact.fieldDefs) {
                addIndexedFieldWrite(new FieldWrite(
                        method, field, fact, "field_write",
                        fieldWriteSources(method, fact, field),
                        "assignment writes field"));
            }
            for (String mutatedField : fieldsMutatedByInvoke(
                    facts, fact.unitIndex)) {
                addIndexedFieldWrite(new FieldWrite(
                        method, mutatedField, fact, "field_mutation",
                        fieldMutationSources(method, fact, mutatedField),
                        "mutator call updates object stored in field"));
            }
            MethodSig sig = parseMethodSig(fact.invoke);
            if (sig == null || !isApplicationClassName(sig.owner)) {
                continue;
            }
            String receiver = canonical(method,
                    invokeBaseLocal(fact.unitText));
            List<String> actuals = canonicalPositionList(method,
                    actualInvokeArgs(fact.unitText));
            if ("<init>".equals(sig.name)) {
                addIndexedConstructorCallsite(new ConstructorCallsite(
                        method, sig.raw, fact, receiver, actuals));
            } else if (!"<clinit>".equals(sig.name)) {
                addIndexedMethodCallsite(new MethodCallsite(
                        method, sig.raw, fact, receiver, actuals,
                        canonicalList(method, fact.defs)));
            }
        }
    }

    private List<String> fieldWriteSources(String method, Fact fact, String field) {
        List<String> raw = new ArrayList<>();
        raw.addAll(localValueUses(fact));
        raw.addAll(actualInvokeArgs(fact.unitText));
        raw.addAll(fact.fieldUses);
        return canonicalSourcesExcludingField(method, raw, field);
    }

    private List<String> fieldMutationSources(String method, Fact fact, String field) {
        List<String> raw = new ArrayList<>();
        raw.addAll(actualInvokeArgs(fact.unitText));
        raw.addAll(fact.fieldUses);
        List<String> sources = canonicalSourcesExcludingField(method, raw, field);
        if (sources.isEmpty()) {
            sources.add(factNode(fact));
        }
        return sources;
    }

    private List<String> canonicalSourcesExcludingField(String method,
                                                        Collection<String> raw,
                                                        String field) {
        List<String> sources = new ArrayList<>();
        for (String value : raw) {
            String canonical = canonical(method, value);
            if (ignoreNode(canonical)
                    || canonical.equals(field)
                    || canonical.contains(field)) {
                continue;
            }
            sources.add(canonical);
        }
        return sources;
    }

    private Set<String> fieldsMutatedByInvoke(List<Fact> facts, int factIndex) {
        Set<String> mutatedFields = new LinkedHashSet<>();
        Fact fact = facts.get(factIndex);
        if (!isFieldMutator(fact)) {
            return mutatedFields;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) {
            return mutatedFields;
        }
        for (String field : fieldsAliasedByLocal(facts, factIndex, receiver)) {
            if (isCanonicalField(field)) {
                mutatedFields.add(field);
            }
        }
        return mutatedFields;
    }

    private Set<String> fieldsAliasedByLocal(List<Fact> facts, int beforeIndex,
                                             String local) {
        Set<String> fields = new LinkedHashSet<>();
        Set<String> work = new LinkedHashSet<>();
        work.add(local);
        for (int i = beforeIndex - 1; i >= 0; i--) {
            Fact fact = facts.get(i);
            Set<String> defs = localNames(fact.defs);
            if (!intersectsLocal(work, defs)) {
                continue;
            }
            fields.addAll(fact.fieldUses);
            fields.addAll(fact.fieldDefs);
            work.addAll(localNames(localValueUses(fact)));
            work.addAll(localNames(actualInvokeArgs(fact.unitText)));
            if (returnsBackedCollectionView(fact)) {
                String invokeBase = invokeBaseLocal(fact.unitText);
                if (invokeBase != null) {
                    work.add(invokeBase);
                }
            }
        }
        return fields;
    }

    /**
     * Models only Java collection APIs whose returned object is specified
     * to remain backed by the receiver.  Propagating aliases through every
     * instance-call result would be unsound; these view/iterator methods
     * are the narrow bridge needed to connect an iterator mutation back to
     * the collection (and ultimately a receiver field) that owns it.
     */
    private boolean returnsBackedCollectionView(Fact fact) {
        MethodSig invoked = parseMethodSig(fact.invoke);
        if (invoked == null || fact.defs.isEmpty()
                || invokeBaseLocal(fact.unitText) == null) {
            return false;
        }
        String owner = invoked.owner;
        String name = invoked.name;
        if (owner.startsWith("java.util.")
                && (owner.contains("Map")
                || "java.util.Hashtable".equals(owner))) {
            return "entrySet".equals(name)
                    || "keySet".equals(name)
                    || "values".equals(name)
                    || "navigableKeySet".equals(name)
                    || "descendingKeySet".equals(name);
        }
        return owner.startsWith("java.util.")
                && ("iterator".equals(name)
                || "listIterator".equals(name)
                || "descendingIterator".equals(name));
    }

    private boolean isFieldMutator(Fact fact) {
        MethodSig sig = parseMethodSig(fact.invoke);
        if (sig == null) {
            return false;
        }
        String name = sig.name;
        return "put".equals(name)
                || "putAll".equals(name)
                || "remove".equals(name)
                || "clear".equals(name)
                || "add".equals(name)
                || "addAll".equals(name)
                || "set".equals(name)
                || "replace".equals(name)
                || "compute".equals(name)
                || "computeIfAbsent".equals(name)
                || "computeIfPresent".equals(name)
                || "merge".equals(name)
                || "offer".equals(name)
                || "poll".equals(name);
    }

    private boolean isCanonicalField(String value) {
        if (value == null || !value.startsWith("<") || !value.endsWith(">")) {
            return false;
        }
        if (parseMethodSig(value) != null) {
            return false;
        }
        return FIELD_PATTERN.matcher(value).matches();
    }

    private boolean isApplicationField(String value) {
        if (!isCanonicalField(value)) {
            return false;
        }
        return isApplicationClassName(fieldOwner(value));
    }

    private boolean isApplicationClassName(String className) {
        SootClass owner = classesByName.get(className);
        return owner != null && owner.isApplicationClass();
    }

    private void processInvoke(String callerMethod, Fact fact,
                               List<String> defs,
                               Set<String> callerRelevant) {
        MethodSig callee = parseMethodSig(fact.invoke);
        if (callee == null) {
            return;
        }
        processSemanticContainerOperation(callerMethod, fact,
                callee, defs, callerRelevant);
        processAccessorInvoke(callerMethod, fact, callee, defs,
                callerRelevant);
        List<String> actuals = canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText));
        processConstructorObjectInvoke(callerMethod, fact, callee,
                actuals, callerRelevant);
        boolean dynamicDispatch = !resolveDispatchTargets(callee)
                .isEmpty();
        boolean modeledContainerResult =
                JavaContainerTypes.symbolicResultOperation(callee.raw);
        boolean expandableCallee = isExpandableMethod(callee.raw);
        SootMethod calleeMethod = expandableCallee ? methodsBySignature.get(callee.raw) : null;
        boolean runtimeRecursiveCaller =
                runtimeRecursiveMethods.contains(callerMethod);
        if (expandableCallee && (selectedMethods.size() < maxMethods
                || runtimeRecursiveMethods.contains(callee.raw))) {
            loadMethod(calleeMethod);
        }
        Set<String> calleeRelevant = expandableCallee
                ? relevant(callee.raw)
                : Collections.emptySet();
        if (expandableCallee) {
            processReceiverSideEffectInvoke(callerMethod, fact,
                    callee, callerRelevant, calleeRelevant);
        }

        if (!dynamicDispatch) {
            propagateCallArguments("call_argument",
                    "method call actual flows to callee formal",
                    callerMethod, fact, callee.raw, callee, actuals,
                    callerRelevant, calleeRelevant, expandableCallee);
            if (!modeledContainerResult) {
                propagateCallReturns("call_return",
                        "callee return flows to caller local",
                        callerMethod, fact, callee.raw, defs,
                        callerRelevant, calleeRelevant, expandableCallee,
                        false);
            }
        }
        if (expandableCallee && runtimeRecursiveCaller
                && selectedMethods.contains(callee.raw)
                && !calleeRelevant.isEmpty()) {
            admitRuntimeRecursiveMethod(callee.raw);
        }
        processRpcInvoke(callerMethod, fact, callee, defs, actuals,
                callerRelevant);
        processDispatchInvoke(callerMethod, fact, callee, defs, actuals,
                callerRelevant);
    }

    private boolean propagateCallArguments(
            String kind, String evidence, String callerMethod, Fact fact,
            String targetMethod, MethodSig target, List<String> actuals,
            Set<String> callerRelevant, Set<String> targetRelevant,
            boolean targetExpandable) {
        boolean relevantFlow = false;
        int count = Math.min(actuals.size(), target.params.size());
        for (int index = 0; index < count; index++) {
            String actual = actuals.get(index);
            if (ignoreNode(actual)) {
                continue;
            }
            String formal = formalParam(target, index);
            boolean formalExact = targetExpandable
                    && targetRelevant.contains(formal);
            boolean formalProjected = targetExpandable
                    && containsProjection(targetRelevant, formal);
            boolean actualHit = callerRelevant.contains(actual)
                    || containsProjection(callerRelevant, actual);
            if (!formalExact && !formalProjected && !actualHit) {
                continue;
            }
            relevantFlow = true;
            addEdge(kind, actual, formal, callerMethod, fact, evidence);
            if (formalExact) {
                callerRelevant.add(actual);
            }
            if (actualHit && targetExpandable) {
                targetRelevant.add(formal);
                selectedMethods.add(targetMethod);
            }
        }
        return relevantFlow;
    }

    private void propagateCallReturns(
            String kind, String evidence, String callerMethod, Fact fact,
            String targetMethod, List<String> defs,
            Set<String> callerRelevant, Set<String> targetRelevant,
            boolean targetExpandable, boolean forceExpansion) {
        String returnNode = targetMethod + ".return";
        for (String def : defs) {
            boolean callerHit = callerRelevant.contains(def)
                    || containsProjection(callerRelevant, def);
            if (!callerHit && !forceExpansion) {
                continue;
            }
            addEdge(kind, returnNode, def, callerMethod, fact, evidence);
            if (callerHit && targetExpandable || forceExpansion) {
                targetRelevant.add(returnNode);
                selectedMethods.add(targetMethod);
            }
            if (forceExpansion) {
                callerRelevant.add(def);
            }
        }
    }

    /**
     * Closes the operands of the Java collection operations modeled by the
     * VM. Generic invoke handling deliberately excludes library receivers:
     * an arbitrary instance method need not return anything derived from its
     * receiver. A modeled container result, however, is a function of the
     * receiver state and its call arguments. Keeping that ordinary dataflow
     * in the slice lets the receiver become one canonical region live-in;
     * the VM's {@code ContainerRelation} owns its value semantics.
     */
    private void processSemanticContainerOperation(
            String callerMethod, Fact fact, MethodSig callee,
            List<String> defs, Set<String> callerRelevant) {
        if (callee == null || defs.isEmpty()
                || !(JavaContainerTypes.symbolicResultOperation(callee.raw)
                || isSemanticContainerProjection(callee))) {
            return;
        }
        List<String> relevantDefs = new ArrayList<>();
        for (String def : defs) {
            if (!ignoreNode(def) && (callerRelevant.contains(def)
                    || containsProjection(callerRelevant, def))) {
                relevantDefs.add(def);
            }
        }
        if (relevantDefs.isEmpty()) return;

        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) return;
        String receiverNode = canonical(callerMethod, receiver);
        if (ignoreNode(receiverNode)) return;
        for (String def : relevantDefs) {
            addEdgeInternal("container_projection", receiverNode, def,
                    callerMethod, fact,
                    "modeled Java container result depends on receiver state",
                    false);
        }
        callerRelevant.add(receiverNode);

        for (String argument : canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText))) {
            if (ignoreNode(argument)) continue;
            for (String def : relevantDefs) {
                addEdgeInternal("container_argument", argument, def,
                        callerMethod, fact,
                        "modeled Java container result depends on argument",
                        false);
            }
            callerRelevant.add(argument);
        }
    }

    private boolean isSemanticContainerProjection(MethodSig method) {
        if (method == null) return false;
        if (javaMapContractOwner(method.owner)
                && method.params.isEmpty()) {
            if ("values".equals(method.name)
                    && "java.util.Collection".equals(
                    method.returnType)) {
                return true;
            }
            if ("keySet".equals(method.name)
                    && "java.util.Set".equals(method.returnType)) {
                return true;
            }
            if ("entrySet".equals(method.name)
                    && "java.util.Set".equals(method.returnType)) {
                return true;
            }
        }
        return javaCollectionContractOwner(method.owner)
                && "toArray".equals(method.name)
                && method.returnType.endsWith("[]")
                && (method.params.isEmpty()
                || (method.params.size() == 1
                && method.params.get(0).endsWith("[]")));
    }

    private boolean javaMapContractOwner(String owner) {
        return "java.util.Map".equals(owner)
                || "java.util.SortedMap".equals(owner)
                || "java.util.NavigableMap".equals(owner)
                || "java.util.concurrent.ConcurrentMap".equals(owner)
                || "java.util.concurrent.ConcurrentNavigableMap".equals(
                owner);
    }

    private boolean javaCollectionContractOwner(String owner) {
        return "java.util.Collection".equals(owner)
                || "java.util.List".equals(owner)
                || "java.util.Set".equals(owner)
                || "java.util.SortedSet".equals(owner)
                || "java.util.NavigableSet".equals(owner)
                || "java.util.Queue".equals(owner)
                || "java.util.Deque".equals(owner);
    }

    /**
     * A Map.get result depends on both the lookup key and the map state.
     * Ordinary instance-call handling intentionally ignores a concrete
     * receiver identity; that rule is incorrect for a semantic container,
     * where receiver contents are data.  Model that dependency here so an
     * exception guard on the result can discover both keyId and allKeys
     * without naming either variable in target.yaml.
     */
    private void processConstructorObjectInvoke(String callerMethod, Fact fact,
                                                MethodSig callee,
                                                List<String> actuals,
                                                Set<String> callerRelevant) {
        if (!"<init>".equals(callee.name)) {
            return;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) {
            return;
        }
        String callerReceiver = canonical(callerMethod, receiver);
        boolean exactReceiverDemand = callerRelevant.contains(callerReceiver);
        boolean projectedReceiverDemand = containsProjection(callerRelevant,
                callerReceiver);
        if (!exactReceiverDemand && !projectedReceiverDemand) {
            return;
        }
        if (projectedReceiverDemand) {
            processConstructorLeafFieldInitializers(callerMethod, fact, callee,
                    actuals, callerReceiver, callerRelevant);
        }
        if (!exactReceiverDemand) {
            return;
        }
        for (String actual : actuals) {
            if (ignoreNode(actual)) {
                continue;
            }
            addEdge("constructor_argument_object", actual, callerReceiver,
                    callerMethod, fact,
                    "constructor actual contributes to initialized receiver object");
            callerRelevant.add(actual);
        }
    }

    /**
     * Projects a demanded scalar leaf of a newly initialized object back
     * to the constructor parameter that initializes the first field in the
     * path.
     *
     * <p>This is deliberately narrower than treating the constructed
     * object reference as symbolic.  For {@code new Product(id, key)} and
     * a demand on {@code product.currentKey.keyId}, the emitted source is
     * {@code key.keyId}; for {@code product.keyId}, it is {@code id}.  The
     * binding is admitted only when Soot proves an intraprocedural
     * parameter-to-{@code this.field} assignment in that exact constructor
     * and the resulting leaf types agree.</p>
     */
    private void processConstructorLeafFieldInitializers(
            String callerMethod, Fact fact, MethodSig constructor,
            List<String> actuals, String callerReceiver,
            Set<String> callerRelevant) {
        Set<String> suffixes = projectionSuffixesForBase(callerReceiver);
        if (suffixes.isEmpty()) {
            return;
        }
        Map<String, Set<Integer>> parametersByField =
                constructorParametersByInitializedField(constructor.raw);
        if (parametersByField.isEmpty()) {
            return;
        }

        for (String suffix : suffixes) {
            if (!callerRelevant.contains(callerReceiver + suffix)
                    || !isAllowedFieldPathSuffix(suffix)
                    || !isScalarLeafProjection(callerReceiver + suffix)) {
                continue;
            }
            List<String> fields = fieldPathNames(suffix);
            if (fields.isEmpty()) {
                continue;
            }
            Set<Integer> parameters = parametersByField.get(fields.get(0));
            if (parameters == null || parameters.size() != 1) {
                // A union of constructor parameters is a dependency, but
                // it is not the exact leaf-owner relation required for an
                // automatic SMT port.  Leave it concrete at runtime.
                continue;
            }
            int parameter = parameters.iterator().next();
            if (parameter < 0 || parameter >= actuals.size()) {
                continue;
            }
            String actual = actuals.get(parameter);
            if (ignoreNode(actual)) {
                continue;
            }
            String remaining = fieldPathSuffix(fields, 1, fields.size());
            String source = actual + remaining;
            String target = callerReceiver + suffix;
            String sourceType = cellValueType(source);
            String targetType = cellValueType(target);
            if (sourceType.isEmpty() || targetType.isEmpty()
                    || !erasedTypeName(sourceType).equals(
                    erasedTypeName(targetType))) {
                continue;
            }
            addEdge("constructor_field_initialization", source, target,
                    callerMethod, fact,
                    "Soot-proven constructor parameter initializes demanded scalar leaf field");
            callerRelevant.add(source);
        }
    }

    private boolean isScalarLeafProjection(String projection) {
        String type = cellValueType(projection);
        return isPrimitiveType(type) || "java.lang.String".equals(type);
    }

    /** Returns exact constructor parameters that may initialize each this field. */
    private Map<String, Set<Integer>> constructorParametersByInitializedField(
            String constructorSignature) {
        SootMethod constructor = methodsBySignature.get(constructorSignature);
        if (constructor == null || !constructor.isConcrete()) {
            return Collections.emptyMap();
        }
        Body body;
        try {
            body = constructor.retrieveActiveBody();
        } catch (RuntimeException exception) {
            return Collections.emptyMap();
        }

        Map<Local, Set<Integer>> origins = new LinkedHashMap<>();
        Set<Local> thisAliases = new LinkedHashSet<>();
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof IdentityStmt)) {
                continue;
            }
            IdentityStmt identity = (IdentityStmt) unit;
            if (!(identity.getLeftOp() instanceof Local)) {
                continue;
            }
            Local left = (Local) identity.getLeftOp();
            if (identity.getRightOp() instanceof ParameterRef) {
                origins.computeIfAbsent(left, ignored -> new LinkedHashSet<>())
                        .add(((ParameterRef) identity.getRightOp()).getIndex());
            } else if (identity.getRightOp() instanceof ThisRef) {
                thisAliases.add(left);
            }
        }

        boolean changed = true;
        while (changed) {
            changed = false;
            for (Unit unit : body.getUnits()) {
                if (!(unit instanceof AssignStmt)) {
                    continue;
                }
                AssignStmt assignment = (AssignStmt) unit;
                Value left = assignment.getLeftOp();
                Value right = assignment.getRightOp();
                if (left instanceof Local) {
                    Set<Integer> rightOrigins = parameterOrigins(right,
                            origins);
                    if (!rightOrigins.isEmpty()) {
                        changed |= origins.computeIfAbsent((Local) left,
                                ignored -> new LinkedHashSet<>())
                                .addAll(rightOrigins);
                    }
                    if (right instanceof Local
                            && thisAliases.contains((Local) right)) {
                        changed |= thisAliases.add((Local) left);
                    } else if (right instanceof CastExpr
                            && ((CastExpr) right).getOp() instanceof Local
                            && thisAliases.contains((Local) ((CastExpr) right)
                            .getOp())) {
                        changed |= thisAliases.add((Local) left);
                    }
                }
            }
        }

        Map<String, Set<Integer>> result = new LinkedHashMap<>();
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)
                    || !(((AssignStmt) unit).getLeftOp()
                    instanceof InstanceFieldRef)) {
                continue;
            }
            AssignStmt assignment = (AssignStmt) unit;
            InstanceFieldRef field = (InstanceFieldRef) assignment.getLeftOp();
            if (!(field.getBase() instanceof Local)
                    || !thisAliases.contains((Local) field.getBase())) {
                continue;
            }
            Set<Integer> fieldOrigins = parameterOrigins(
                    assignment.getRightOp(), origins);
            if (!fieldOrigins.isEmpty()) {
                result.computeIfAbsent(field.getFieldRef().name(),
                        ignored -> new LinkedHashSet<>())
                        .addAll(fieldOrigins);
            }
        }
        return result;
    }

    private Set<Integer> parameterOrigins(Value value,
                                          Map<Local, Set<Integer>> origins) {
        if (value instanceof Local) {
            Set<Integer> found = origins.get((Local) value);
            return found == null ? Collections.emptySet() : found;
        }
        if (value instanceof CastExpr) {
            return parameterOrigins(((CastExpr) value).getOp(), origins);
        }
        Set<Integer> result = new LinkedHashSet<>();
        for (ValueBox box : value.getUseBoxes()) {
            if (box.getValue() instanceof Local) {
                Set<Integer> found = origins.get((Local) box.getValue());
                if (found != null) {
                    result.addAll(found);
                }
            }
        }
        return result;
    }

    private void processReceiverSideEffectInvoke(String callerMethod, Fact fact,
                                                 MethodSig callee,
                                                 Set<String> callerRelevant,
                                                 Set<String> calleeRelevant) {
        if ("<init>".equals(callee.name)) {
            return;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) {
            return;
        }
        String callerReceiver = canonical(callerMethod, receiver);
        Set<String> suffixes = projectionSuffixesForBase(callerReceiver);
        if (suffixes.isEmpty()) {
            return;
        }
        String calleeThis = methodThisNode(callee.raw);
        if (calleeThis == null) {
            return;
        }
        for (String suffix : suffixes) {
            if (!isAllowedFieldPathSuffix(suffix)
                    || !canCarryProjection(callerReceiver, suffix)
                    || !canCarryProjection(calleeThis, suffix)
                    || !calleeMayWriteReceiverProjection(callee.raw, suffix)) {
                continue;
            }
            String callerProjection = callerReceiver + suffix;
            if (!callerRelevant.contains(callerProjection)) {
                continue;
            }
            String calleeProjection = calleeThis + suffix;
            addEdge("method_receiver_field_effect", calleeProjection,
                    callerProjection, callerMethod, fact,
                    "instance method may write receiver field observed by caller");
            calleeRelevant.add(calleeProjection);
            selectedMethods.add(callee.raw);
        }
    }

    private boolean calleeMayWriteReceiverProjection(String method, String suffix) {
        if (!isAllowedFieldPathSuffix(suffix)) {
            return false;
        }
        String key = method + "\n" + suffix;
        Boolean cached = receiverProjectionWriteSummary.get(key);
        if (cached != null) {
            return cached;
        }
        boolean result = calleeMayWriteReceiverProjection(method, suffix,
                new LinkedHashSet<>());
        receiverProjectionWriteSummary.put(key, result);
        return result;
    }

    private boolean calleeMayWriteReceiverProjection(String method, String suffix,
                                                    Set<String> visiting) {
        String key = method + "\n" + suffix;
        Boolean cached = receiverProjectionWriteSummary.get(key);
        if (cached != null) {
            return cached;
        }
        if (!visiting.add(key)) {
            return false;
        }
        try {
            List<Fact> facts = summaryFacts(method);
            String thisNode = methodThisNode(method, facts);
            if (facts.isEmpty() || thisNode == null) {
                return cacheReceiverProjectionWrite(key, false);
            }
            List<String> fields = fieldPathNames(suffix);
            if (fields.isEmpty()) {
                return cacheReceiverProjectionWrite(key, false);
            }

            for (int depth = 0; depth < fields.size(); depth++) {
                String prefix = fieldPathSuffix(fields, 0, depth);
                String writtenField = fields.get(depth);
                Set<String> aliases = projectionAliases(method, facts, thisNode, prefix);
                if (aliases.isEmpty()) {
                    continue;
                }
                for (Fact fact : facts) {
                    for (InstanceFieldAccess access : fact.instanceFieldDefs) {
                        String base = canonical(method, access.base);
                        if (aliases.contains(base)
                                && writtenField.equals(fieldNameFromSignature(access.field))) {
                            return cacheReceiverProjectionWrite(key, true);
                        }
                    }
                }
            }

            Set<String> fullProjectionAliases =
                    projectionAliases(method, facts, thisNode, suffix);
            for (Fact fact : facts) {
                String receiver = canonical(method, invokeBaseLocal(fact.unitText));
                if (isFieldMutator(fact) && fullProjectionAliases.contains(receiver)) {
                    return cacheReceiverProjectionWrite(key, true);
                }
            }

            for (Fact fact : facts) {
                MethodSig target = parseMethodSig(fact.invoke);
                if (target == null || "<init>".equals(target.name)
                        || "<clinit>".equals(target.name)
                        || !isApplicationClassName(target.owner)) {
                    continue;
                }
                String receiver = canonical(method, invokeBaseLocal(fact.unitText));
                if (ignoreNode(receiver)) {
                    continue;
                }
                for (int depth = 0; depth < fields.size(); depth++) {
                    String prefix = fieldPathSuffix(fields, 0, depth);
                    Set<String> aliases = projectionAliases(method, facts, thisNode,
                            prefix);
                    if (!aliases.contains(receiver)) {
                        continue;
                    }
                    String remaining = fieldPathSuffix(fields, depth, fields.size());
                    if (!remaining.isEmpty()
                            && calleeMayWriteReceiverProjection(target.raw, remaining,
                            visiting)) {
                        return cacheReceiverProjectionWrite(key, true);
                    }
                }
            }
            return cacheReceiverProjectionWrite(key, false);
        } finally {
            visiting.remove(key);
        }
    }

    private boolean cacheReceiverProjectionWrite(String key, boolean value) {
        receiverProjectionWriteSummary.put(key, value);
        return value;
    }

    private List<Fact> summaryFacts(String method) {
        List<Fact> facts = factsByMethod.get(method);
        if (facts != null) {
            return facts;
        }
        SootMethod sootMethod = methodsBySignature.get(method);
        return sootMethod == null ? Collections.emptyList() : factsFromMethod(sootMethod);
    }

    private String methodThisNode(String method, List<Fact> facts) {
        for (Fact fact : facts) {
            Matcher matcher = Pattern.compile("([$]?[A-Za-z_][A-Za-z0-9_]*)\\s*:=\\s*@this:")
                    .matcher(fact.unitText);
            if (matcher.find()) {
                return canonical(method, matcher.group(1));
            }
        }
        return null;
    }

    private Set<String> projectionAliases(String method, List<Fact> facts,
                                          String base, String suffix) {
        String key = method + "\n" + base + "\n" + suffix;
        Set<String> cached = projectionAliasCache.get(key);
        if (cached != null) {
            return cached;
        }
        Set<String> aliases = closeLocalAliases(method, facts,
                Collections.singleton(base));
        for (String field : fieldPathNames(suffix)) {
            Set<String> next = new LinkedHashSet<>();
            for (Fact fact : facts) {
                for (InstanceFieldAccess access : fact.instanceFieldUses) {
                    String accessBase = canonical(method, access.base);
                    if (!aliases.contains(accessBase)
                            || !field.equals(fieldNameFromSignature(access.field))) {
                        continue;
                    }
                    for (String def : canonicalList(method, fact.defs)) {
                        if (isLocalCell(def)) {
                            next.add(def);
                        }
                    }
                }
            }
            aliases = closeLocalAliases(method, facts, next);
            if (aliases.isEmpty()) {
                break;
            }
        }
        projectionAliasCache.put(key, aliases);
        return aliases;
    }

    private Set<String> closeLocalAliases(String method, List<Fact> facts,
                                          Collection<String> seeds) {
        Set<String> aliases = new LinkedHashSet<>();
        for (String seed : seeds) {
            if (!ignoreNode(seed)) {
                aliases.add(seed);
            }
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Fact fact : facts) {
                List<String> defs = canonicalList(method, fact.defs);
                List<String> uses = canonicalList(method, nonInvokeUses(fact));
                boolean hit = false;
                for (String def : defs) {
                    if (aliases.contains(def)) {
                        hit = true;
                        break;
                    }
                }
                if (!hit) {
                    for (String use : uses) {
                        if (aliases.contains(use)) {
                            hit = true;
                            break;
                        }
                    }
                }
                if (!hit) {
                    continue;
                }
                for (String def : defs) {
                    if (isLocalCell(def)) {
                        changed |= aliases.add(def);
                    }
                }
                for (String use : uses) {
                    if (isLocalCell(use)) {
                        changed |= aliases.add(use);
                    }
                }
            }
        }
        return aliases;
    }

    private boolean isLocalCell(String cell) {
        if (cell == null || isFieldProjection(cell)) {
            return false;
        }
        return cell.contains("::");
    }

    private String fieldPathSuffix(List<String> fields, int start, int end) {
        if (fields == null || start >= end) {
            return "";
        }
        StringBuilder builder = new StringBuilder();
        for (int i = Math.max(0, start); i < Math.min(fields.size(), end); i++) {
            builder.append("#field:").append(fields.get(i));
        }
        return builder.toString();
    }

    private void processAccessorInvoke(String callerMethod, Fact fact,
                                       MethodSig callee, List<String> defs,
                                       Set<String> callerRelevant) {
        if (callee == null || defs.isEmpty()) {
            return;
        }
        StructuralFieldAccessor accessor = structuralFieldAccessor(callee);
        if (accessor == null) {
            return;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) {
            return;
        }
        SootField declaredField = accessor.field;
        String fieldName = declaredField.getName();
        String receiverNode = canonical(callerMethod, receiver);
        String receiverField = fieldProjection(receiverNode, fieldName);
        if (ignoreNode(receiverField)) {
            return;
        }
        String projectedType = declaredField.getType().toString();
        if (projectedType.isEmpty()
                || !erasedTypeName(projectedType).equals(
                erasedTypeName(callee.returnType))) {
            return;
        }
        boolean defExactHit = exactIntersects(callerRelevant, defs);
        boolean defProjectionHit = projectionIntersects(callerRelevant, defs);
        boolean defHit = defExactHit || defProjectionHit;
        if (!defHit) {
            return;
        }
        for (String def : defs) {
            if (ignoreNode(def)) {
                continue;
            }
            if (declaredField != null) {
                String declaredFieldNode = declaredField.getSignature();
                addEdge("accessor_field_return", declaredFieldNode,
                        def, callerMethod, fact,
                        "accessor return reads canonical declared field");
                annotateAccessorDeclaredFieldEdge(declaredFieldNode, def,
                        callerMethod, fact, declaredField,
                        accessor.implementation);
            }
            addEdge("accessor_field_return", receiverField, def,
                    callerMethod, fact,
                    "accessor return reads receiver-local field projection");
            if (declaredField != null) {
                annotateAccessorDeclaredFieldEdge(receiverField, def,
                        callerMethod, fact, declaredField,
                        accessor.implementation);
            }
        }
        if (defExactHit && canOpenFieldFromPlainValues(defs)) {
            callerRelevant.add(receiverField);
            if (declaredField != null) {
                callerRelevant.add(declaredField.getSignature());
            }
        }
        if (defProjectionHit) {
            callerRelevant.add(receiverField);
            if (declaredField != null) {
                callerRelevant.add(declaredField.getSignature());
            }
        }
    }

    private void annotateAccessorDeclaredFieldEdge(
            String from, String to, String method, Fact fact,
            SootField field, SootMethod accessor) {
        StaticEdge edge = emittedEdgeRows.get(edgeKey(
                "accessor_field_return", from, to, method, fact));
        if (edge == null || field == null) {
            return;
        }
        edge.put("declaredFieldSignature", field.getSignature());
        if (accessor != null) {
            edge.put("accessorImplementationMethod",
                    accessor.getSignature());
        }
    }

    /**
     * Attaches the resolved Java declaration to one exact direct field
     * read.  Requested-output planning intentionally refuses to turn a
     * textual {@code <owner: type name>} cell into a replayable field
     * input without this Soot authority: inherited fields, shadowing and
     * receiver projections would otherwise be indistinguishable.
     *
     * <p>Both the canonical declared-field row and its receiver-sensitive
     * companion are annotated.  The former is the materializable scalar
     * frontier; the latter participates in exact alias/object proofs.
     * No class or fixture names are consulted.</p>
     */
    private void annotateDirectDeclaredFieldEdge(
            String kind, String from, String to, String method, Fact fact,
            String fieldSignature) {
        StaticEdge edge = emittedEdgeRows.get(edgeKey(kind,
                from, to, method, fact));
        String owner = fieldOwner(fieldSignature);
        String name = fieldNameFromSignature(fieldSignature);
        SootField field = resolveDeclaredField(owner, name);
        if (edge == null || field == null
                || !field.getSignature().equals(fieldSignature)) {
            return;
        }
        edge.put("declaredFieldSignature", field.getSignature());
        edge.put("declaredFieldStatic", field.isStatic());
    }

    /**
     * Resolves one method declaration inherited by the invocation owner.
     * This is declaration lookup only; callers that need virtual-dispatch
     * uniqueness must additionally inspect application overrides.
     */
    private SootMethod resolveDeclaredMethod(MethodSig methodSignature) {
        if (methodSignature == null || methodSignature.owner.isEmpty()) {
            return null;
        }
        return resolveInHierarchy(methodSignature.owner, sootClass -> {
            for (SootMethod method : sootClass.getMethods()) {
                if (!methodSignature.name.equals(method.getName())
                        || !erasedTypeName(
                        methodSignature.returnType).equals(
                        erasedTypeName(method.getReturnType()
                                .toString()))
                        || method.getParameterCount()
                        != methodSignature.params.size()) {
                    continue;
                }
                boolean parametersMatch = true;
                for (int index = 0;
                     index < methodSignature.params.size();
                     index++) {
                    if (!erasedTypeName(
                            methodSignature.params.get(index))
                            .equals(erasedTypeName(method
                                    .getParameterType(index)
                                    .toString()))) {
                        parametersMatch = false;
                        break;
                    }
                }
                if (parametersMatch) {
                    return method;
                }
            }
            return null;
        });
    }

    /**
     * Returns the unique application implementation that can receive this
     * invocation in the closed Soot world.  An inherited declaration counts
     * as the implementation, while every concrete override below the
     * invocation owner is an additional candidate.  Ambiguity deliberately
     * disables the accessor shortcut.
     */
    private SootMethod uniqueApplicationImplementation(MethodSig callee) {
        if (callee == null || callee.owner.isEmpty()) {
            return null;
        }
        SootClass owner = classesByName.get(callee.owner);
        if (owner == null) {
            return null;
        }
        Set<SootMethod> candidates = Collections.newSetFromMap(
                new IdentityHashMap<SootMethod, Boolean>());
        SootMethod declared = resolveDeclaredMethod(callee);
        if (eligibleApplicationImplementation(declared)) {
            candidates.add(declared);
        }
        List<SootMethod> implementations = concreteMethodsBySubSignature.get(
                methodSubSignature(callee));
        if (implementations != null) {
            for (SootMethod implementation : implementations) {
                if (eligibleApplicationImplementation(implementation)
                        && classImplementsOrExtends(
                        implementation.getDeclaringClass(), callee.owner)) {
                    candidates.add(implementation);
                }
            }
        }
        return candidates.size() == 1
                ? candidates.iterator().next() : null;
    }

    private boolean eligibleApplicationImplementation(SootMethod method) {
        return method != null && method.isConcrete() && !method.isStatic()
                && method.getDeclaringClass().isApplicationClass();
    }

    /**
     * Recognizes a field accessor from its complete Jimple body, never from
     * class or method spelling.  Accepted bodies contain exactly one
     * {@code @this} identity, transparent local copies/checkcasts, one read
     * of an instance field rooted at that receiver, and one return of the
     * read value.  Every other unit or value shape falls back to ordinary
     * application-method analysis.
     */
    private StructuralFieldAccessor structuralFieldAccessor(
            MethodSig callee) {
        if (callee == null) {
            return null;
        }
        if (structuralFieldAccessors.containsKey(callee.raw)) {
            return structuralFieldAccessors.get(callee.raw);
        }
        StructuralFieldAccessor resolved = inspectStructuralFieldAccessor(
                callee, uniqueApplicationImplementation(callee));
        structuralFieldAccessors.put(callee.raw, resolved);
        return resolved;
    }

    private StructuralFieldAccessor inspectStructuralFieldAccessor(
            MethodSig callee, SootMethod method) {
        if (method == null || method.isStatic() || method.isNative()
                || method.isSynchronized() || !method.isConcrete()
                || !callee.params.isEmpty() || method.getParameterCount() != 0
                || "void".equals(erasedTypeName(callee.returnType))) {
            return null;
        }
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return null;
        }
        if (!body.getTraps().isEmpty()) {
            return null;
        }

        Set<Local> receiverAliases = new LinkedHashSet<>();
        Set<Local> valueAliases = new LinkedHashSet<>();
        SootField field = null;
        boolean receiverIdentitySeen = false;
        boolean returnSeen = false;
        for (Unit unit : body.getUnits()) {
            if (unit instanceof IdentityStmt) {
                IdentityStmt identity = (IdentityStmt) unit;
                if (receiverIdentitySeen
                        || !(identity.getLeftOp() instanceof Local)
                        || !(identity.getRightOp() instanceof ThisRef)) {
                    return null;
                }
                receiverAliases.add((Local) identity.getLeftOp());
                receiverIdentitySeen = true;
                continue;
            }
            if (unit instanceof AssignStmt) {
                AssignStmt assignment = (AssignStmt) unit;
                if (!(assignment.getLeftOp() instanceof Local)) {
                    return null;
                }
                Local target = (Local) assignment.getLeftOp();
                Value source = assignment.getRightOp();
                boolean sourceIsReceiverAlias = source instanceof Local
                        && receiverAliases.contains((Local) source);
                boolean sourceIsValueAlias = source instanceof Local
                        && valueAliases.contains((Local) source);
                boolean castSourceIsReceiverAlias = source instanceof CastExpr
                        && ((CastExpr) source).getOp() instanceof Local
                        && receiverAliases.contains(
                        (Local) ((CastExpr) source).getOp());
                boolean castSourceIsValueAlias = source instanceof CastExpr
                        && ((CastExpr) source).getOp() instanceof Local
                        && valueAliases.contains(
                        (Local) ((CastExpr) source).getOp());
                receiverAliases.remove(target);
                valueAliases.remove(target);
                if (source instanceof Local) {
                    if (sourceIsReceiverAlias) {
                        receiverAliases.add(target);
                    } else if (sourceIsValueAlias) {
                        valueAliases.add(target);
                    } else {
                        return null;
                    }
                    continue;
                }
                if (source instanceof CastExpr
                        && ((CastExpr) source).getOp() instanceof Local) {
                    if (castSourceIsReceiverAlias) {
                        receiverAliases.add(target);
                    } else if (castSourceIsValueAlias) {
                        valueAliases.add(target);
                    } else {
                        return null;
                    }
                    continue;
                }
                if (source instanceof InstanceFieldRef) {
                    InstanceFieldRef fieldRead = (InstanceFieldRef) source;
                    if (field != null
                            || !(fieldRead.getBase() instanceof Local)
                            || !receiverAliases.contains(
                            (Local) fieldRead.getBase())) {
                        return null;
                    }
                    try {
                        field = fieldRead.getField();
                    } catch (RuntimeException unresolved) {
                        return null;
                    }
                    if (field == null || field.isStatic()
                            || !field.getDeclaringClass()
                            .isApplicationClass()) {
                        return null;
                    }
                    valueAliases.add(target);
                    continue;
                }
                return null;
            }
            if (unit instanceof ReturnStmt) {
                Value returned = ((ReturnStmt) unit).getOp();
                if (returnSeen || !(returned instanceof Local)
                        || !valueAliases.contains((Local) returned)) {
                    return null;
                }
                returnSeen = true;
                continue;
            }
            return null;
        }
        if (!receiverIdentitySeen || !returnSeen || field == null
                || !erasedTypeName(field.getType().toString()).equals(
                erasedTypeName(callee.returnType))
                || !erasedTypeName(method.getReturnType().toString()).equals(
                erasedTypeName(callee.returnType))) {
            return null;
        }
        return new StructuralFieldAccessor(method, field);
    }

    private void processRpcInvoke(String callerMethod, Fact fact,
                                  MethodSig callee, List<String> defs,
                                  List<String> actuals,
                                  Set<String> callerRelevant) {
        List<String> targets = rpcTargetsBySource.getOrDefault(callee.raw,
                Collections.emptyList());
        if (targets.isEmpty()) {
            return;
        }
        int count = 0;
        for (String target : targets) {
            if (target.equals(callee.raw)) {
                continue;
            }
            if (count++ >= MAX_RPC_TARGETS_PER_CALL) {
                break;
            }
            SootMethod targetMethod = methodsBySignature.get(target);
            if (targetMethod == null) {
                continue;
            }
            if (selectedMethods.size() < maxMethods) {
                loadMethod(targetMethod);
            }
            MethodSig targetSig = parseMethodSig(target);
            if (targetSig == null) {
                continue;
            }
            Set<String> targetRelevant = relevant(target);
            propagateCallArguments("rpc_argument",
                    "RPC actual flows to discovered server-side formal",
                    callerMethod, fact, target, targetSig, actuals,
                    callerRelevant, targetRelevant, true);
            propagateCallReturns("rpc_return",
                    "discovered server-side RPC return flows to caller",
                    callerMethod, fact, target, defs,
                    callerRelevant, targetRelevant, true, false);
        }
    }

    private void processDispatchInvoke(String callerMethod, Fact fact,
                                       MethodSig callee, List<String> defs,
                                       List<String> actuals,
                                       Set<String> callerRelevant) {
        List<String> targetMethods = resolveDispatchTargets(callee);
        if (targetMethods.isEmpty()) {
            return;
        }
        RuntimeDispatchSelection runtimeSelection =
                runtimeDispatchSelection(callerMethod, fact, callee,
                        targetMethods);
        if (runtimeSelection.blocked()) {
            return;
        }
        if (runtimeSelection.unique()) {
            targetMethods = runtimeSelection.targets;
        } else {
            targetMethods = CausynthPipeline.conservativeDispatchTargets(
                    targetMethods);
        }
        if (!runtimeSelection.unique()
                && targetMethods.size()
                > MAX_DISPATCH_TARGETS_PER_CALL) {
            return;
        }
        int count = 0;
        for (String targetMethod : targetMethods) {
            if (targetMethod.equals(callee.raw)) {
                continue;
            }
            if (count++ >= MAX_DISPATCH_TARGETS_PER_CALL) {
                break;
            }
            SootMethod sootMethod = methodsBySignature.get(targetMethod);
            if (sootMethod == null) {
                continue;
            }
            if (runtimeSelection.unique()) {
                if (!admitRuntimeRecursiveMethod(targetMethod)) {
                    continue;
                }
            } else if (selectedMethods.size() < maxMethods) {
                loadMethod(sootMethod);
            }
            MethodSig targetSig = parseMethodSig(targetMethod);
            if (targetSig == null) {
                continue;
            }
            Set<String> targetRelevant = relevant(targetMethod);
            boolean runtimeReturnExpansion = runtimeSelection.unique()
                    && !callerRelevant.isEmpty()
                    && !defs.isEmpty()
                    && canCarryProjectedFieldContainer(
                            targetSig.returnType);
            boolean callRelevant = intersects(callerRelevant, defs)
                    || runtimeReturnExpansion;
            callRelevant |= propagateCallArguments("dispatch_argument",
                    "interface/virtual dispatch actual flows to concrete formal",
                    callerMethod, fact, targetMethod, targetSig, actuals,
                    callerRelevant, targetRelevant, true);
            propagateCallReturns("dispatch_return",
                    "concrete dispatch return flows to caller",
                    callerMethod, fact, targetMethod, defs,
                    callerRelevant, targetRelevant, true,
                    runtimeReturnExpansion);
            String callerReceiver = canonical(callerMethod,
                    invokeBaseLocal(fact.unitText));
            String targetThis = methodThisNode(targetMethod);
            if (callRelevant && targetThis != null
                    && !ignoreNode(callerReceiver)) {
                addEdge("dispatch_receiver", callerReceiver, targetThis,
                        callerMethod, fact,
                        "runtime receiver selects and aliases concrete dispatch target");
                callerRelevant.add(callerReceiver);
                targetRelevant.add(targetThis);
                selectedMethods.add(targetMethod);
            }
        }
    }

    /**
     * Resolves an interface callback using the concrete object captured at
     * its registration site.  Class-hierarchy dispatch alone sees both
     * encrypted and general-purpose PasswordFunction implementations in
     * the same handle() body.  Only the registration whose implementation
     * can reach the configured exception belongs to this backward slice.
     */
    private RuntimeDispatchSelection runtimeDispatchSelection(
            String callerMethod, Fact fact, MethodSig callee,
            List<String> staticTargets) {
        String siteId = stableSiteId(callerMethod,
                fact == null ? -1 : fact.unitIndex, "dispatch");
        Set<String> actualCallees =
                runtimeDispatchEvidence.lookup(callerMethod, siteId,
                        callee == null ? "" : callee.raw);
        if (actualCallees == null) {
            return RuntimeDispatchSelection.staticFallback(staticTargets);
        }
        if (actualCallees.size() != 1) {
            return RuntimeDispatchSelection.blockedSelection();
        }
        String actual = actualCallees.iterator().next();
        if (!staticTargets.contains(actual)) {
            return RuntimeDispatchSelection.blockedSelection();
        }
        return RuntimeDispatchSelection.runtimeUnique(actual);
    }

    private boolean admitRuntimeRecursiveMethod(String method) {
        if (runtimeRecursiveMethods.contains(method)) {
            return true;
        }
        if (runtimeRecursiveMethods.size()
                >= MAX_RUNTIME_RECURSIVE_METHODS) {
            return false;
        }
        SootMethod sootMethod = methodsBySignature.get(method);
        if (sootMethod == null || !sootMethod.isConcrete()) {
            return false;
        }
        runtimeRecursiveMethods.add(method);
        selectedMethods.add(method);
        if (!factsByMethod.containsKey(method) && !loadMethod(sootMethod)) {
            return false;
        }
        return true;
    }

    private List<String> resolveDispatchTargets(MethodSig callee) {
        if (callee == null || skipDispatchOwner(callee.owner)
                || isRpcProtocolName(callee.owner)) {
            return Collections.emptyList();
        }
        SootClass owner = classesByName.get(callee.owner);
        if (owner == null || (!owner.isInterface() && !owner.isAbstract())) {
            return Collections.emptyList();
        }
        List<SootMethod> concreteMethods = concreteMethodsBySubSignature
                .get(callee.returnType + " " + callee.name + "("
                        + String.join(",", callee.params) + ")");
        if (concreteMethods == null) {
            concreteMethods = concreteMethodsBySubSignature
                    .get(methodSubSignature(callee));
        }
        if (concreteMethods == null) {
            return Collections.emptyList();
        }
        List<String> targets = new ArrayList<>();
        for (SootMethod concreteMethod : concreteMethods) {
            SootClass concreteClass = concreteMethod.getDeclaringClass();
            if (concreteClass.isApplicationClass()
                    && classImplementsOrExtends(concreteClass, callee.owner)) {
                targets.add(concreteMethod.getSignature());
            }
        }
        return targets;
    }

    private String methodSubSignature(MethodSig sig) {
        return sig.returnType + " " + sig.name + "("
                + String.join(",", sig.params) + ")";
    }

    private boolean skipDispatchOwner(String owner) {
        return owner == null
                || owner.startsWith("java.")
                || owner.startsWith("javax.")
                || owner.startsWith("com.google.")
                || owner.startsWith("org.slf4j.");
    }

    private boolean isRpcProtocolName(String className) {
        return className != null
                && (className.contains("Protocol")
                || className.contains("protocolPB")
                || className.endsWith("PB"));
    }

    private void expandRpcCallers(String targetMethod) {
        List<String> sources = rpcSourcesByTarget.get(targetMethod);
        expandPolymorphicCallers(targetMethod, sources, false);
    }

    private void expandDispatchCallers(String targetMethod) {
        expandPolymorphicCallers(targetMethod,
                resolveDispatchSources(targetMethod), true);
    }

    private void expandPolymorphicCallers(String targetMethod,
                                          List<String> sourceMethods,
                                          boolean dispatch) {
        if (sourceMethods == null || sourceMethods.isEmpty()) {
            return;
        }
        MethodSig targetSig = parseMethodSig(targetMethod);
        if (targetSig == null) {
            return;
        }
        Set<String> targetRelevant = relevant(targetMethod);
        String returnNode = targetMethod + ".return";
        boolean returnRelevant = targetRelevant.contains(returnNode)
                || containsProjection(targetRelevant, returnNode);
        String targetThis = methodThisNode(targetMethod);
        Set<String> targetThisProjectionSuffixes =
                projectionSuffixesForBase(targetThis);
        boolean targetThisRelevant = dispatch && targetThis != null
                && (targetRelevant.contains(targetThis)
                || !targetThisProjectionSuffixes.isEmpty());
        buildGlobalStaticIndex();
        for (String sourceMethod : sourceMethods) {
            List<MethodCallsite> callsites = methodCallersByCallee.get(sourceMethod);
            if (callsites == null) {
                continue;
            }
            for (MethodCallsite callsite : callsites) {
                if (selectedMethods.size() >= maxMethods
                        && (!dispatch || !runtimeRecursiveMethods.contains(
                        targetMethod))) {
                    break;
                }
                if (dispatch) {
                    MethodSig sourceSig = parseMethodSig(sourceMethod);
                    RuntimeDispatchSelection selection =
                            runtimeDispatchSelection(callsite.method,
                                    callsite.fact, sourceSig,
                                    resolveDispatchTargets(sourceSig));
                    if (selection.blocked()
                            || selection.unique()
                            && !selection.targets.contains(targetMethod)
                            || selection.unique()
                            && !admitRuntimeRecursiveMethod(targetMethod)) {
                        continue;
                    }
                }
                SootMethod callerMethod = methodsBySignature.get(callsite.method);
                if (callerMethod != null) {
                    loadMethod(callerMethod);
                }
                Set<String> callerRelevant = relevant(callsite.method);
                String prefix = dispatch ? "DISPATCH" : "RPC";
                expandCallerArguments(prefix + "_CALLER_PARAM",
                        dispatch ? "dispatch_caller_argument"
                                : "rpc_caller_argument",
                        dispatch
                                ? "interface/virtual caller actual reaches concrete formal"
                                : "RPC caller actual reaches discovered server-side formal",
                        targetMethod, sourceMethod, targetSig, targetRelevant,
                        callsite, callerRelevant);
                if (returnRelevant && expandOnce(prefix + "_CALLER_RETURN",
                        targetMethod, sourceMethod, callsite.method,
                        callsite.fact.unitIndex)) {
                    expandCallerReturn(dispatch
                                    ? "dispatch_caller_return"
                                    : "rpc_caller_return",
                            returnNode, callsite.defs, callsite.method,
                            callsite.fact, callerRelevant,
                            dispatch
                                    ? "interface/virtual caller receives relevant concrete return"
                                    : "RPC caller receives relevant server-side return");
                }
                if (targetThisRelevant) {
                    expandCallerReceiverFields(true, targetMethod,
                            targetThis, targetThisProjectionSuffixes,
                            callsite);
                }
            }
        }
    }

    private void expandCallerArguments(
            String demandKind, String edgeKind, String evidence,
            String targetMethod, String sourceMethod, MethodSig target,
            Set<String> targetRelevant, MethodCallsite callsite,
            Set<String> callerRelevant) {
        int count = Math.min(callsite.actuals.size(),
                target.params.size());
        for (int index = 0; index < count; index++) {
            String formal = formalParam(target, index);
            if (!targetRelevant.contains(formal)
                    && !containsProjection(targetRelevant, formal)
                    || !expandOnce(demandKind, targetMethod, sourceMethod,
                    index, callsite.method, callsite.fact.unitIndex)) {
                continue;
            }
            String actual = callsite.actuals.get(index);
            if (ignoreNode(actual)) {
                continue;
            }
            addEdge(edgeKind, actual, formal, callsite.method,
                    callsite.fact, evidence);
            callerRelevant.add(actual);
            selectedMethods.add(callsite.method);
        }
    }

    private void expandCallerReturn(String kind, String returnNode,
                                    List<String> defs, String callerMethod,
                                    Fact fact, Set<String> callerRelevant,
                                    String evidence) {
        if (defs == null || defs.isEmpty() || ignoreNode(returnNode)) {
            return;
        }
        for (String def : defs) {
            if (ignoreNode(def)) {
                continue;
            }
            addEdge(kind, returnNode, def, callerMethod, fact, evidence);
            callerRelevant.add(def);
            selectedMethods.add(callerMethod);
        }
    }

    private void expandCallerReceiverFields(
            boolean dispatch, String targetMethod, String targetThis,
            Set<String> suffixes, MethodCallsite callsite) {
        if (targetThis == null || callsite == null
                || ignoreNode(callsite.receiver)) {
            return;
        }
        String demand = dispatch ? "DISPATCH_CALLER_RECEIVER"
                : "METHOD_CALLER_RECEIVER";
        String kind = dispatch ? "dispatch_caller_receiver"
                : "method_receiver";
        if (relevant(targetMethod).contains(targetThis)
                && expandOnce(demand, targetMethod,
                callsite.method, callsite.fact.unitIndex)) {
            addEdge(kind, callsite.receiver,
                    targetThis, callsite.method, callsite.fact,
                    dispatch
                            ? "interface/virtual receiver aliases concrete this"
                            : "instance method receiver flows to callee this");
            relevant(callsite.method).add(callsite.receiver);
            selectedMethods.add(callsite.method);
        }
        for (String suffix : suffixes) {
            if (dispatch && !isAllowedFieldPathSuffix(suffix)) {
                continue;
            }
            if (!expandOnce(demand + "_FIELD", targetMethod,
                    callsite.method, callsite.fact.unitIndex, suffix)) {
                continue;
            }
            String callerProjection = callsite.receiver + suffix;
            String targetProjection = targetThis + suffix;
            addEdge(kind + "_field", callerProjection,
                    targetProjection, callsite.method, callsite.fact,
                    dispatch
                            ? "interface/virtual receiver field aliases "
                            + "concrete this field"
                            : "instance method receiver field flows to "
                            + "callee this field");
            relevant(callsite.method).add(callerProjection);
            selectedMethods.add(callsite.method);
        }
    }

    private List<String> resolveDispatchSources(String targetMethod) {
        MethodSig targetSig = parseMethodSig(targetMethod);
        if (targetSig == null || skipDispatchOwner(targetSig.owner)) {
            return Collections.emptyList();
        }
        SootClass targetClass = classesByName.get(targetSig.owner);
        if (targetClass == null) {
            return Collections.emptyList();
        }
        List<String> sources = new ArrayList<>();
        String subSignature = methodSubSignature(targetSig);
        for (SootClass candidate : classesByName.values()) {
            if (!candidate.isApplicationClass()
                    || skipDispatchOwner(candidate.getName())
                    || isRpcProtocolName(candidate.getName())
                    || (!candidate.isInterface() && !candidate.isAbstract())
                    || !classImplementsOrExtends(targetClass, candidate.getName())) {
                continue;
            }
            for (SootMethod method : candidate.getMethods()) {
                if (subSignature.equals(method.getSubSignature())) {
                    sources.add(method.getSignature());
                }
            }
        }
        return sources;
    }

    private void propagateProjectedEdge(StaticEdge edge) {
        if (!projectableEdge(edge)) {
            return;
        }
        addProjectedEdgesForObjectFlow(edge.kind, edge.from, edge.to,
                edge.method, null, edge);
    }

    private void indexProjectableEdge(StaticEdge edge) {
        if (!projectableEdge(edge)) {
            return;
        }
        projectableEdgesByEndpoint.computeIfAbsent(edge.from,
                ignored -> new ArrayList<>()).add(edge);
        if (!edge.from.equals(edge.to)) {
            projectableEdgesByEndpoint.computeIfAbsent(edge.to,
                    ignored -> new ArrayList<>()).add(edge);
        }
    }

    private boolean projectableEdge(StaticEdge edge) {
        return supportsProjectedPropagation(edge.kind)
                && (!"local_def_use".equals(edge.kind)
                || edge.row.get("invoke") == null)
                && canCarryProjectedFields(edge.from)
                && canCarryProjectedFields(edge.to);
    }

    private void enqueueProjectableEdges(String endpoint) {
        for (StaticEdge edge : projectableEdgesByEndpoint
                .getOrDefault(endpoint, Collections.emptyList())) {
            dirtyProjectedEdges.putIfAbsent(edge.id, edge);
        }
    }

    private boolean isExpandableMethod(String signature) {
        SootMethod method = methodsBySignature.get(signature);
        MethodSig sig = parseMethodSig(signature);
        return method != null
                && method.isConcrete()
                && method.getDeclaringClass().isApplicationClass()
                && !method.getDeclaringClass().isInterface()
                && !method.getDeclaringClass().isAbstract()
                && structuralFieldAccessor(sig) == null;
    }

    private Set<String> relevant(String method) {
        return relevantByMethod.computeIfAbsent(method, DirtyRelevantSet::new);
    }

    private boolean expandOnce(String kind, Object... identity) {
        StringBuilder key = new StringBuilder(kind);
        for (Object value : identity) {
            key.append('\n').append(String.valueOf(value));
        }
        return expandedDemands.add(key.toString());
    }

    private void markDirty(String method) {
        if (method != null && selectedMethods.contains(method)) {
            dirtyMethods.add(method);
        }
    }

    private final class MethodWorkSet extends LinkedHashSet<String> {
        @Override
        public boolean add(String method) {
            if (!super.add(method)) return false;
            markDirty(method);
            return true;
        }

    }

    private final class DirtyRelevantSet extends LinkedHashSet<String> {
        private final String method;

        private DirtyRelevantSet(String method) {
            this.method = method;
        }

        @Override
        public boolean add(String cell) {
            if (!super.add(cell)) return false;
            markDirty(method);
            indexRelevantProjection(cell);
            return true;
        }

    }

    private List<String> nonInvokeUses(Fact fact) {
        List<String> uses = new ArrayList<>();
        for (String use : fact.uses) {
            if (!use.startsWith("virtualinvoke ")
                    && !use.startsWith("interfaceinvoke ")
                    && !use.startsWith("specialinvoke ")
                    && !use.startsWith("staticinvoke ")) {
                uses.add(use);
            }
        }
        return uses;
    }

    private List<String> localValueUses(Fact fact) {
        Set<String> instanceFieldBases = instanceFieldBases(fact);
        String invokeBase = invokeBaseLocal(fact.unitText);
        Set<String> applicationInvokeArgs = new LinkedHashSet<>();
        MethodSig invoked = parseMethodSig(fact.invoke);
        boolean applicationInvoke = invoked != null
                && isApplicationClassName(invoked.owner);
        boolean valueLikeLibraryInvoke = isValueLikeLibraryInvoke(invoked);
        if (applicationInvoke) {
            applicationInvokeArgs.addAll(actualInvokeArgs(fact.unitText));
        }
        Set<String> uses = new LinkedHashSet<>();
        for (String use : nonInvokeUses(fact)) {
            // Soot exposes both a composite expression and each of its
            // leaf operands through Unit.getUseBoxes().  Only the leaves
            // are data-flow cells.  Treating an expression such as
            // "$l1 cmp $l0" as an additional cell creates a false
            // external frontier even though $l1 and $l0 already define
            // the comparison result.
            if (!atomicDataflowUse(use)
                    || instanceFieldBases.contains(use)
                    || (!valueLikeLibraryInvoke && use.equals(invokeBase))
                    || applicationInvokeArgs.contains(use)
                    || isFieldAccessValue(use)) {
                continue;
            }
            // Unit.getUseBoxes() can report both a cast expression and
            // its leaf local.  The cast is an in-region operation, not a
            // second data-flow cell.  Preserve the leaf so the backward
            // slice does not invent an unqualified "(T) local" live-in.
            String leafLocal = localName(use);
            uses.add(leafLocal == null ? use : leafLocal);
        }
        return new ArrayList<>(uses);
    }

    private boolean atomicDataflowUse(String value) {
        if (value == null) {
            return false;
        }
        String trimmed = value.trim();
        return localName(trimmed) != null
                || isFieldAccessValue(trimmed)
                || trimmed.startsWith("@parameter")
                || "null".equals(trimmed)
                || "true".equals(trimmed)
                || "false".equals(trimmed)
                || trimmed.matches("-?\\d+(?:[lLfFdD])?")
                || trimmed.startsWith("\"");
    }

    private boolean isValueLikeLibraryInvoke(MethodSig invoked) {
        if (invoked == null) {
            return false;
        }
        String owner = invoked.owner;
        if (invoked.params.isEmpty()
                && (("java.lang.Byte".equals(owner)
                        && "byteValue".equals(invoked.name))
                || ("java.lang.Short".equals(owner)
                        && "shortValue".equals(invoked.name))
                || ("java.lang.Integer".equals(owner)
                        && "intValue".equals(invoked.name))
                || ("java.lang.Long".equals(owner)
                        && "longValue".equals(invoked.name))
                || ("java.lang.Character".equals(owner)
                        && "charValue".equals(invoked.name))
                || ("java.lang.Float".equals(owner)
                        && "floatValue".equals(invoked.name))
                || ("java.lang.Double".equals(owner)
                        && "doubleValue".equals(invoked.name)))) {
            return true;
        }
        if ("java.lang.String".equals(owner)) {
            return true;
        }
        return "java.lang.StringBuilder".equals(owner)
                || "java.lang.StringBuffer".equals(owner)
                || "java.lang.AbstractStringBuilder".equals(owner);
    }

    private Set<String> instanceFieldBases(Fact fact) {
        Set<String> bases = new LinkedHashSet<>();
        for (InstanceFieldAccess access : fact.instanceFieldUses) {
            bases.add(access.base);
        }
        for (InstanceFieldAccess access : fact.instanceFieldDefs) {
            bases.add(access.base);
        }
        return bases;
    }

    private boolean isFieldAccessValue(String value) {
        if (value == null) {
            return false;
        }
        String trimmed = value.trim();
        return isCanonicalField(trimmed)
                || (trimmed.contains(".<")
                && trimmed.contains(":")
                && trimmed.endsWith(">"));
    }

    private List<String> canonicalList(String method, Collection<String> values) {
        List<String> result = new ArrayList<>();
        for (String value : values) {
            String canonical = canonical(method, value);
            if (!ignoreNode(canonical)) {
                result.add(canonical);
            }
        }
        return result;
    }

    private List<String> canonicalPositionList(String method, Collection<String> values) {
        List<String> result = new ArrayList<>();
        for (String value : values) {
            result.add(canonical(method, value));
        }
        return result;
    }

    private String canonical(String method, String value) {
        if (value == null) {
            return "";
        }
        String trimmed = value.trim();
        if (trimmed.isEmpty()) {
            return "";
        }
        Matcher parameter = Pattern.compile("@parameter(\\d+):\\s*(.+)").matcher(trimmed);
        if (parameter.find()) {
            return method + ".param" + parameter.group(1) + ":" + parameter.group(2);
        }
        if (trimmed.startsWith("<")) {
            return trimmed;
        }
        if ("null".equals(trimmed)
                || "true".equals(trimmed)
                || "false".equals(trimmed)) {
            return trimmed;
        }
        if (trimmed.matches("[$]?[A-Za-z_][A-Za-z0-9_]*")) {
            return method + "::" + trimmed;
        }
        return trimmed;
    }

    private List<String> parameterNodesFromUnit(MethodSig sig, String unit) {
        List<String> nodes = new ArrayList<>();
        Matcher matcher = Pattern.compile("@parameter(\\d+)").matcher(unit);
        while (matcher.find()) {
            int index = Integer.parseInt(matcher.group(1));
            if (index >= 0 && index < sig.params.size()) {
                nodes.add(formalParam(sig, index));
            }
        }
        return nodes;
    }

    private String formalParam(MethodSig sig, int index) {
        return sig.raw + ".param" + index + ":" + sig.params.get(index);
    }

    private String factNode(Fact fact) {
        return fact.method + "#u" + fact.unitIndex;
    }

    private String methodThisNode(String method) {
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null) {
            return null;
        }
        for (Fact fact : facts) {
            Matcher matcher = Pattern.compile("([$]?[A-Za-z_][A-Za-z0-9_]*)\\s*:=\\s*@this:")
                    .matcher(fact.unitText);
            if (matcher.find()) {
                return canonical(method, matcher.group(1));
            }
        }
        return null;
    }

    private void expandConstructorReceiverFields(String constructor,
                                                 String constructorThis,
                                                 Set<String> suffixes,
                                                 ConstructorCallsite callsite) {
        if (constructorThis == null || ignoreNode(callsite.receiver)) {
            return;
        }
        if (relevant(constructor).contains(constructorThis)
                && expandOnce("CONSTRUCTOR_CALLER_RECEIVER", constructor,
                callsite.method, callsite.fact.unitIndex)) {
            addEdge("constructor_receiver", callsite.receiver,
                    constructorThis,
                    callsite.method, callsite.fact,
                    "constructor receiver aliases constructor this");
            relevant(callsite.method).add(callsite.receiver);
            selectedMethods.add(callsite.method);
        }
        for (String suffix : suffixes) {
            if (!expandOnce("CONSTRUCTOR_CALLER_RECEIVER_FIELD", constructor,
                    callsite.method, callsite.fact.unitIndex, suffix)) {
                continue;
            }
            String constructorProjection = constructorThis + suffix;
            String callerProjection = callsite.receiver + suffix;
            addEdge("constructor_receiver_field", constructorProjection,
                    callerProjection, callsite.method, callsite.fact,
                    "constructor-written this field is visible on caller receiver");
            relevant(callsite.method).add(callerProjection);
            selectedMethods.add(callsite.method);
        }
    }

    private String fieldProjection(String base, String fieldName) {
        if (base == null || fieldName == null || fieldName.isEmpty()
                || ignoreNode(base)) {
            return "";
        }
        return base + "#field:" + fieldName;
    }

    private boolean isFieldProjection(String node) {
        return node != null && node.contains("#field:");
    }

    private Set<String> projectionSuffixesForBase(String base) {
        return relevantProjectionSuffixesByBase.getOrDefault(base,
                Collections.emptySet());
    }

    private void indexRelevantProjection(String cell) {
        int projection = cell == null ? -1 : cell.indexOf("#field:");
        while (projection >= 0) {
            String base = cell.substring(0, projection);
            relevantProjectionSuffixesByBase.computeIfAbsent(
                    base,
                    ignored -> new LinkedHashSet<>())
                    .add(cell.substring(projection));
            enqueueProjectableEdges(base);
            projection = cell.indexOf("#field:", projection + 7);
        }
    }

    private void addProjectedRelevance(String method, String node) {
        if (ignoreNode(node)) {
            return;
        }
        String owner = methodForCell(node, method);
        relevant(owner).add(node);
    }

    private String methodForCell(String cell, String fallback) {
        String base = stripFieldProjection(cell);
        int local = base.indexOf("::");
        if (local > 0) {
            return base.substring(0, local);
        }
        int ret = base.indexOf(">.return");
        if (ret > 0) {
            return base.substring(0, ret + 1);
        }
        int param = base.indexOf(">.param");
        if (param > 0) {
            return base.substring(0, param + 1);
        }
        int unit = base.indexOf("#u");
        if (unit > 0) {
            return base.substring(0, unit);
        }
        return fallback;
    }

    private String stripFieldProjection(String cell) {
        int index = cell == null ? -1 : cell.indexOf("#field:");
        return index < 0 ? cell : cell.substring(0, index);
    }

    private String fieldProjectionPath(String cell) {
        int index = cell == null ? -1 : cell.indexOf("#field:");
        return index < 0 ? "" : cell.substring(index);
    }

    private static String fieldNameFromSignature(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = Pattern.compile("<[^:]+:\\s+.+\\s+([^\\s>]+)>")
                .matcher(fieldSignature);
        return matcher.find() ? matcher.group(1) : "";
    }

    private void addProjectedEdgesForObjectFlow(String kind, String fromText,
                                                String toText, String method,
                                                Fact fact,
                                                StaticEdge baseEdge) {
        if (!supportsProjectedPropagation(kind)
                || ("local_def_use".equals(kind) && fact != null
                && fact.invoke != null)
                || !canCarryProjectedFields(fromText)
                || !canCarryProjectedFields(toText)) {
            return;
        }
        String baseEdgeId = baseEdge == null ? "" : baseEdge.id;
        Set<String> suffixes = new LinkedHashSet<>();
        suffixes.addAll(projectionSuffixesForBase(fromText));
        suffixes.addAll(projectionSuffixesForBase(toText));
        if (suffixes.isEmpty()) {
            return;
        }
        for (String suffix : suffixes) {
            if (!isAllowedFieldPathSuffix(suffix)
                    || !canCarryProjection(fromText, suffix)
                    || !canCarryProjection(toText, suffix)) {
                continue;
            }
            String fromProjection = fromText + suffix;
            String toProjection = toText + suffix;
            if (fromProjection.equals(toProjection)) {
                continue;
            }
            if (!baseEdgeId.isEmpty()
                    && !expandOnce("PROJECTED_EDGE_SUFFIX", baseEdgeId,
                    suffix)) {
                continue;
            }
            addEdgeInternal("projected_" + kind, fromProjection, toProjection,
                    method, fact,
                    "field path propagated along object edge " + baseEdgeId,
                    false, baseEdge);
            if (isRelevantProjection(toText, suffix)) {
                addProjectedRelevance(method, fromProjection);
            }
            if (isRelevantProjection(fromText, suffix)) {
                addProjectedRelevance(method, toProjection);
            }
        }
    }

    private boolean isAllowedFieldPathSuffix(String suffix) {
        List<String> fields = fieldPathNames(suffix);
        if (fields.isEmpty() || fields.size() > MAX_FIELD_PATH_DEPTH) {
            return false;
        }
        Set<String> seen = new LinkedHashSet<>();
        for (String field : fields) {
            if (!seen.add(field)) {
                return false;
            }
        }
        return true;
    }

    private boolean isRelevantProjection(String base, String suffix) {
        return projectionSuffixesForBase(base).contains(suffix);
    }

    private boolean supportsProjectedPropagation(String kind) {
        if (kind == null || kind.startsWith("projected_")) {
            return false;
        }
        if ("method_receiver".equals(kind)
                || "constructor_receiver".equals(kind)
                || "method_receiver_field".equals(kind)
                || "constructor_receiver_field".equals(kind)) {
            return false;
        }
        return !"control_depends_on".equals(relationForKind(kind))
                && !kind.startsWith("seed")
                && !kind.contains("guard")
                && !kind.contains("throw");
    }

    private boolean canCarryProjectedFields(String node) {
        if (ignoreNode(node)) {
            return false;
        }
        String type = cellValueType(node);
        if (!type.isEmpty()) {
            return canCarryProjectedFieldContainer(type);
        }
        String base = stripFieldProjection(node);
        if (isCanonicalField(base)) {
            return canCarryProjectedFieldContainer(fieldType(base));
        }
        int param = base.indexOf(">.param");
        if (param > 0) {
            String paramType = base.substring(base.indexOf(':', param) + 1);
            return canCarryProjectedFieldContainer(paramType);
        }
        if (base.endsWith(".return")) {
            int marker = base.indexOf(">.return");
            MethodSig sig = parseMethodSig(base.substring(0, marker + 1));
            return sig != null && canCarryProjectedFieldContainer(sig.returnType);
        }
        if (base.contains("::")) {
            String local = base.substring(base.indexOf("::") + 2);
            return local.startsWith("$r") || local.startsWith("r")
                    || local.startsWith("$stack") || isFieldProjection(node);
        }
        MethodSig methodSig = parseMethodSig(base);
        if (methodSig != null) {
            return false;
        }
        return isFieldProjection(node);
    }

    private boolean canCarryProjection(String base, String suffix) {
        if (suffix == null || suffix.isEmpty()) {
            return true;
        }
        return !cellValueType(base + suffix).isEmpty();
    }

    private boolean canCarryProjectedFieldContainer(String type) {
        if (type == null || type.trim().isEmpty() || isPrimitiveType(type)) {
            return false;
        }
        String erased = erasedTypeName(type);
        if (erased.isEmpty() || erased.endsWith("[]")) {
            return false;
        }
        if (isApplicationClassName(erased)) {
            return true;
        }
        return !erased.startsWith("java.")
                && !erased.startsWith("javax.")
                && !erased.startsWith("sun.")
                && !erased.startsWith("com.google.")
                && !erased.startsWith("org.slf4j.");
    }

    private String cellValueType(String cell) {
        if (cell == null || cell.isEmpty()) {
            return "";
        }
        String root = stripFieldProjection(cell);
        String type = rootCellValueType(root);
        if (type.isEmpty()) {
            return "";
        }
        for (String fieldName : fieldPathNames(fieldProjectionPath(cell))) {
            type = resolveFieldType(type, fieldName);
            if (type.isEmpty()) {
                return "";
            }
        }
        return type;
    }

    private String rootCellValueType(String root) {
        if (root == null || root.isEmpty()) {
            return "";
        }
        String directFieldType = fieldType(root);
        if (!directFieldType.isEmpty()) {
            return directFieldType;
        }
        if (root.startsWith("@this:")) {
            return root.substring(root.indexOf(':') + 1).trim();
        }
        int param = root.indexOf(">.param");
        if (param > 0) {
            int colon = root.indexOf(':', param);
            return colon > 0 ? root.substring(colon + 1).trim() : "";
        }
        if (root.endsWith(".return")) {
            int marker = root.indexOf(">.return");
            if (marker > 0) {
                MethodSig sig = parseMethodSig(root.substring(0, marker + 1));
                return sig == null ? "" : sig.returnType;
            }
        }
        int localMarker = root.indexOf("::");
        if (localMarker > 0) {
            String method = root.substring(0, localMarker);
            String local = root.substring(localMarker + 2);
            return localType(method, local);
        }
        return "";
    }

    private List<String> fieldPathNames(String path) {
        if (path == null || path.isEmpty()) {
            return Collections.emptyList();
        }
        List<String> fields = new ArrayList<>();
        Matcher matcher = Pattern.compile("#field:([^#]+)").matcher(path);
        while (matcher.find()) {
            fields.add(matcher.group(1));
        }
        return fields;
    }

    private String localType(String methodSignature, String localName) {
        SootMethod method = methodsBySignature.get(methodSignature);
        if (method == null || localName == null || localName.isEmpty()) {
            return "";
        }
        try {
            Body body = method.retrieveActiveBody();
            for (Local local : body.getLocals()) {
                if (localName.equals(local.getName())) {
                    return local.getType().toString();
                }
            }
        } catch (RuntimeException ignored) {
        }
        return "";
    }

    private String resolveFieldType(String ownerType, String fieldName) {
        SootField field = resolveDeclaredField(ownerType, fieldName);
        return field == null ? "" : field.getType().toString();
    }

    /**
     * Resolves the Java field declaration selected by an accessor through
     * the receiver's class hierarchy.  The invocation owner is not
     * necessarily the declaration owner (for example a subclass may
     * inherit {@code getExpiryDate()} and its backing field), so callers
     * must retain the returned Soot signature instead of rebuilding one
     * from the accessor owner and field name.
     */
    private SootField resolveDeclaredField(String ownerType,
                                           String fieldName) {
        String owner = erasedTypeName(ownerType);
        if (owner.isEmpty() || fieldName == null || fieldName.isEmpty()
                || owner.endsWith("[]")) {
            return null;
        }
        return resolveInHierarchy(owner, sootClass -> {
            for (SootField field : sootClass.getFields()) {
                if (fieldName.equals(field.getName())) {
                    return field;
                }
            }
            return null;
        });
    }

    private <T> T resolveInHierarchy(String owner,
                                     Function<SootClass, T> resolver) {
        SootClass root = classesByName.get(owner);
        if (root == null) {
            try {
                root = Scene.v().getSootClassUnsafe(owner);
            } catch (RuntimeException ignored) {
                return null;
            }
        }
        if (root == null) {
            return null;
        }
        return resolveInHierarchy(root, resolver);
    }

    private <T> T resolveInHierarchy(SootClass root,
                                     Function<SootClass, T> resolver) {
        Set<SootClass> seen = Collections.newSetFromMap(
                new IdentityHashMap<>());
        Deque<SootClass> work = new ArrayDeque<>();
        work.add(root);
        while (!work.isEmpty()) {
            SootClass sootClass = work.removeFirst();
            if (sootClass == null || !seen.add(sootClass)) {
                continue;
            }
            try {
                T resolved = resolver.apply(sootClass);
                if (resolved != null) {
                    return resolved;
                }
                // Prefer the superclass before interfaces, matching Java
                // declaration lookup while retaining interface constants.
                if (sootClass.hasSuperclass()) {
                    work.addFirst(sootClass.getSuperclass());
                }
                for (SootClass iface : sootClass.getInterfaces()) {
                    work.addLast(iface);
                }
            } catch (RuntimeException ignored) {
                return null;
            }
        }
        return null;
    }

    private String erasedTypeName(String type) {
        if (type == null) {
            return "";
        }
        String erased = type.trim();
        int generic = erased.indexOf('<');
        if (generic > 0) {
            erased = erased.substring(0, generic);
        }
        return erased;
    }

    private static String fieldType(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Pattern exactField = Pattern.compile("<[^:]+:\\s+(.+)\\s+[^\\s()>]+>");
        Matcher exact = exactField.matcher(fieldSignature);
        if (exact.matches() && parseMethodSig(fieldSignature) == null) {
            return exact.group(1);
        }
        Matcher embedded = Pattern.compile("\\.<[^:]+:\\s+(.+)\\s+[^\\s()>]+>")
                .matcher(fieldSignature);
        return embedded.find() ? embedded.group(1) : "";
    }

    private boolean isPrimitiveType(String type) {
        if (type == null) {
            return false;
        }
        String trimmed = type.trim();
        return "boolean".equals(trimmed)
                || "byte".equals(trimmed)
                || "char".equals(trimmed)
                || "short".equals(trimmed)
                || "int".equals(trimmed)
                || "long".equals(trimmed)
                || "float".equals(trimmed)
                || "double".equals(trimmed)
                || "void".equals(trimmed);
    }

    private void addEdge(String kind, Object from, Object to, String method,
                         Fact fact, String evidence) {
        addEdgeInternal(kind, from, to, method, fact, evidence, true);
    }

    private void addEdgeInternal(String kind, Object from, Object to,
                                 String method, Fact fact, String evidence,
                                 boolean deriveProjectedEdges) {
        addEdgeInternal(kind, from, to, method, fact, evidence,
                deriveProjectedEdges, null);
    }

    private void addEdgeInternal(String kind, Object from, Object to,
                                 String method, Fact fact, String evidence,
                                 boolean deriveProjectedEdges,
                                 StaticEdge projectionBaseEdge) {
        if (edges.size() >= maxEdges || from == null || to == null) {
            return;
        }
        String fromText = String.valueOf(from);
        String toText = String.valueOf(to);
        boolean sameCellPathGuard =
                ControlDependenceEdgeSupport.permitsSameCellEdge(kind,
                        fromText, toText, fact != null);
        if (ignoreNode(fromText) || ignoreNode(toText)
                || fromText.equals(toText) && !sameCellPathGuard) {
            return;
        }
        String key = edgeKey(kind, fromText, toText, method, fact);
        StaticEdge edge = emittedEdgeRows.get(key);
        boolean added = edge == null;
        if (edge == null) {
            String edgeId = "DF." + edgeCounter++;
            boolean hasProjectionBase = projectionBaseEdge != null;
            String semanticMode = hasProjectionBase
                    ? StaticDataflowEdgeSchema.semanticMode(
                    projectionBaseEdge.row)
                    : StaticDataflowEdgeSchema.ASSERTABLE;
            if (semanticMode.isEmpty()) {
                semanticMode = StaticDataflowEdgeSchema
                        .RUNTIME_VALIDATION_REQUIRED;
            }
            boolean mappingOnly = StaticDataflowEdgeSchema.MAPPING_ONLY
                    .equals(semanticMode);
            boolean assertable = StaticDataflowEdgeSchema.ASSERTABLE
                    .equals(semanticMode);
            String edgeTransferKind = StaticDataflowEdgeSchema.transferKind(
                    kind,
                    fact == null ? "" : fact.unitText,
                    fact == null ? null : fact.invoke,
                    fromText, toText);
            boolean exactDirectCopy = assertable
                    && exactLocalDirectCopy(kind, fromText, toText,
                    method, fact, edgeTransferKind);
            boolean projectedDirectCopy = assertable
                    && exactProjectedDirectCopy(kind, fromText, toText,
                    projectionBaseEdge, edgeTransferKind);
            String relation = exactDirectCopy || projectedDirectCopy
                    ? "value_flow" : relationForKind(kind);
            edge = new StaticEdge(edgeId, kind, fromText, toText, method,
                    object(
                    "schemaVersion", StaticDataflowEdgeSchema.VERSION,
                    "id", edgeId,
                    "kind", kind,
                    "transferKind", edgeTransferKind,
                    "semanticMode", semanticMode,
                    "relation", mappingOnly ? "" : relation,
                    "fromCell", fromText,
                    "toCell", toText,
                    "method", method,
                    "siteId", stableSiteId(method,
                            fact == null ? -1 : fact.unitIndex, kind),
                    "evidence", evidence));
            if (hasProjectionBase) {
                edge.put("projectionBaseEdgeId", projectionBaseEdge.id);
                edge.put("authorityInheritance",
                        "PROJECTED_EDGE_CANNOT_EXCEED_BASE_EDGE_V1");
            }
            if (exactDirectCopy) {
                edge.put("valueFlowAuthority",
                        fact.unit instanceof IdentityStmt
                                ? "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1"
                                : "SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
                edge.put("directCopyKind",
                        fact.unit instanceof IdentityStmt
                                ? "PARAMETER_IDENTITY"
                                : fact.unit instanceof ReturnStmt
                                ? "RETURN_LOCAL" : "LOCAL_ASSIGN_LOCAL");
            } else if (projectedDirectCopy) {
                String baseAuthority = projectionBaseEdge.value(
                        "valueFlowAuthority");
                edge.put("valueFlowAuthority",
                        "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1".equals(
                                baseAuthority)
                                ? "PROJECTED_FROM_SOOT_EXACT_PARAMETER_"
                                + "IDENTITY_BINDING_V1"
                                : "PROJECTED_FROM_SOOT_EXACT_LOCAL_"
                                + "DIRECT_COPY_V1");
                edge.put("baseValueFlowEdgeId", projectionBaseEdge.id);
                edge.put("baseValueFlowAuthority", baseAuthority);
            }
            if (isFieldProjection(fromText) || isFieldProjection(toText)) {
                edge.put("fieldSensitive", true);
                edge.put("objectFromCell", stripFieldProjection(fromText));
                edge.put("objectToCell", stripFieldProjection(toText));
                edge.put("fieldPath", firstNonBlank(
                        fieldProjectionPath(fromText),
                        fieldProjectionPath(toText),
                        ""));
            }
            if (fact != null) {
                edge.put("unitIndex", fact.unitIndex);
                edge.put("unit", fact.unitText);
                if (fact.invoke != null) {
                    edge.put("invoke", fact.invoke);
                }
                edge.putAll(allocationConstructorEvidence(method, fact,
                        fromText));
            }
            edges.add(edge);
            emittedEdgeRows.put(key, edge);
            indexProjectableEdge(edge);
        }
        if (deriveProjectedEdges && added) {
            addProjectedEdgesForObjectFlow(kind, fromText, toText,
                    method, fact, edge);
        }
    }

    /**
     * Proves that one ordinary {@code local_def_use} row is an exact JVM
     * value copy.  A VALUE_PASS label alone is not evidence: field/array
     * reads, casts, invokes, and other expressions can all look like a
     * non-arithmetic pass in rendered Jimple.  Inspect the original Soot
     * statement and require the emitted endpoint pair to be exactly the
     * local operand and its local/return destination.
     */
    private boolean exactLocalDirectCopy(String kind, String fromText,
                                         String toText, String method,
                                         Fact fact,
                                         String edgeTransferKind) {
        if (!"local_def_use".equals(kind)
                || !"VALUE_PASS".equals(edgeTransferKind)
                || fact == null || fact.invoke != null) {
            return false;
        }
        if (fact.unit instanceof ReturnStmt) {
            Value operand = ((ReturnStmt) fact.unit).getOp();
            return operand instanceof Local
                    && canonical(method, operand.toString()).equals(
                    fromText)
                    && (method + ".return").equals(toText);
        }
        if (fact.unit instanceof IdentityStmt) {
            IdentityStmt identity = (IdentityStmt) fact.unit;
            Value left = identity.getLeftOp();
            Value right = identity.getRightOp();
            return left instanceof Local && right instanceof ParameterRef
                    && (method + ".param"
                    + ((ParameterRef) right).getIndex() + ":"
                    + right.getType()).equals(fromText)
                    && canonical(method, left.toString()).equals(toText);
        }
        if (fact.unit instanceof AssignStmt) {
            AssignStmt assignment = (AssignStmt) fact.unit;
            Value left = assignment.getLeftOp();
            Value right = assignment.getRightOp();
            return left instanceof Local && right instanceof Local
                    && canonical(method, right.toString()).equals(
                    fromText)
                    && canonical(method, left.toString()).equals(toText);
        }
        return false;
    }

    /**
     * A projected local copy is exact only as a field-sensitive shadow of
     * an already certified base copy.  This also covers suffixes found in
     * later worklist rounds where the original Soot {@link Fact} is no
     * longer available; no projected kind or text pattern can manufacture
     * value-flow authority by itself.
     */
    private boolean exactProjectedDirectCopy(
            String kind, String fromText, String toText,
            StaticEdge baseEdge, String edgeTransferKind) {
        if (!"projected_local_def_use".equals(kind)
                || !"VALUE_PASS".equals(edgeTransferKind)
                || baseEdge == null
                || !"local_def_use".equals(baseEdge.kind)
                || !"value_flow".equals(baseEdge.value("relation"))
                || !"VALUE_PASS".equals(baseEdge.value("transferKind"))
                || !StaticDataflowEdgeSchema.automaticSemantics(
                baseEdge.row)) {
            return false;
        }
        String authority = baseEdge.value("valueFlowAuthority");
        String copyKind = baseEdge.value("directCopyKind");
        boolean exactLocalCopy = "SOOT_EXACT_LOCAL_DIRECT_COPY_V1".equals(
                authority) && ("LOCAL_ASSIGN_LOCAL".equals(copyKind)
                || "RETURN_LOCAL".equals(copyKind));
        boolean exactParameterIdentity =
                "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1".equals(
                        authority)
                        && "PARAMETER_IDENTITY".equals(copyKind);
        if (!exactLocalCopy && !exactParameterIdentity) {
            return false;
        }
        String fromPath = fieldProjectionPath(fromText);
        String toPath = fieldProjectionPath(toText);
        return !fromPath.isEmpty() && fromPath.equals(toPath)
                && stripFieldProjection(fromText).equals(baseEdge.from)
                && stripFieldProjection(toText).equals(baseEdge.to);
    }

    private String edgeKey(String kind, Object from, Object to,
                           String method, Fact fact) {
        // A concrete Soot unit is part of a causal edge's identity.  The
        // same value endpoints can occur at multiple bytecode/Jimple sites
        // (for example, two branch arms reading the same field into the same
        // merge local, or two calls supplying the same actual to one formal).
        // Collapsing those rows loses exact capture/materialization choices
        // and can make a genuinely ambiguous field read appear unique.
        // Repeated fixed-point visits to the same unit still deduplicate via
        // the stable method/unit site id.  Synthetic edges retain the legacy
        // endpoint identity because they have no concrete site to distinguish.
        String site = fact != null
                ? "\n" + stableSiteId(method, fact.unitIndex, kind) : "";
        return kind + "\n" + String.valueOf(from) + "\n"
                + String.valueOf(to) + "\n" + method + site;
    }

    /**
     * Attaches constructor evidence to a Jimple allocation edge.  A
     * {@code new T} expression alone does not establish the initialized
     * state of the object: the following constructor may accept a source
     * collection or otherwise populate it.  Keeping the exact constructor
     * call on the allocation edge lets later, project-independent region
     * planning distinguish a fresh default-constructed container from an
     * arbitrary allocation without reopening Soot bodies.
     */
    private Map<String, Object> allocationConstructorEvidence(
            String method, Fact allocationFact, String fromCell) {
        Matcher allocation = Pattern.compile("^new\\s+([^\\s]+)$")
                .matcher(fromCell == null ? "" : fromCell.trim());
        if (!allocation.matches()
                || !(allocationFact.unit instanceof AssignStmt)) {
            return Collections.emptyMap();
        }
        String allocatedType = allocation.group(1);
        String local = ((AssignStmt) allocationFact.unit).getLeftOp()
                .toString();
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null || local.isEmpty()) {
            return Collections.emptyMap();
        }
        for (Fact candidate : facts) {
            if (candidate.unitIndex <= allocationFact.unitIndex) {
                continue;
            }
            MethodSig invoked = parseMethodSig(candidate.invoke);
            if (invoked != null && "<init>".equals(invoked.name)
                    && allocatedType.equals(invoked.owner)
                    && local.equals(invokeBaseLocal(candidate.unitText))) {
                return object(
                        "allocationType", allocatedType,
                        "allocationConstructor", candidate.invoke,
                        "allocationConstructorArgumentCount",
                        invoked.params.size(),
                        "allocationConstructorEvidence",
                        "JIMPLE_SPECIALINVOKE_ON_FRESH_LOCAL");
            }
            if (localNames(candidate.defs).contains(local)) {
                break;
            }
        }
        return object(
                "allocationType", allocatedType,
                "allocationConstructorEvidence",
                "CONSTRUCTOR_NOT_PROVEN_BEFORE_REDEFINITION");
    }

    private String relationForKind(String kind) {
        if (kind == null) {
            return "taint_depends_on";
        }
        if (kind.contains("guard") || kind.contains("throw")) {
            return "control_depends_on";
        }
        if (kind.startsWith("container_")
                || kind.contains("field") || kind.contains("argument")
                || kind.contains("return") || kind.contains("rpc")
                || kind.contains("dispatch") || kind.contains("protocol")
                || kind.contains("transfer")) {
            return "value_flow";
        }
        return "taint_depends_on";
    }

    private boolean exactIntersects(Set<String> relevant, Collection<String> values) {
        for (String value : values) {
            if (relevant.contains(value)) {
                return true;
            }
        }
        return false;
    }

    private boolean projectionIntersects(Set<String> relevant,
                                         Collection<String> values) {
        for (String value : values) {
            if (containsProjection(relevant, value)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsProjection(Set<String> relevant, String base) {
        if (base == null || base.isEmpty()) {
            return false;
        }
        String prefix = base + "#field:";
        for (String value : relevant) {
            if (value.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }

    private boolean canOpenFieldFromPlainValues(Collection<String> values) {
        for (String value : values) {
            if (canOpenFieldFromPlainValue(value)) {
                return true;
            }
        }
        return false;
    }

    private boolean canOpenFieldFromPlainValue(String value) {
        String type = cellValueType(value);
        return type.isEmpty() || !canCarryProjectedFieldContainer(type);
    }

    private boolean intersects(Set<String> relevant, List<String> values) {
        for (String value : values) {
            if (relevant.contains(value)
                    || containsProjection(relevant, value)) {
                return true;
            }
        }
        return false;
    }

    private boolean ignoreNode(String value) {
        if (value == null) {
            return true;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty()
                || "null".equals(trimmed)
                || trimmed.matches("-?\\d+")
                || trimmed.startsWith("\"")
                || trimmed.startsWith("staticinvoke ")
                || trimmed.startsWith("virtualinvoke ")
                || trimmed.startsWith("interfaceinvoke ")
                || trimmed.startsWith("specialinvoke ");
    }

    private static final class MethodSig {
        private final String raw;
        private final String owner;
        private final String returnType;
        private final String name;
        private final List<String> params;

        private MethodSig(String raw, String owner, String returnType,
                          String name, List<String> params) {
            this.raw = raw;
            this.owner = owner;
            this.returnType = returnType;
            this.name = name;
            this.params = params;
        }
    }

    private static final class StructuralFieldAccessor {
        private final SootMethod implementation;
        private final SootField field;

        private StructuralFieldAccessor(SootMethod implementation,
                                        SootField field) {
            this.implementation = implementation;
            this.field = field;
        }
    }

    private static final class StaticEdge {
        private final String id;
        private final String kind;
        private final String from;
        private final String to;
        private final String method;
        private final Map<String, Object> row;

        private StaticEdge(String id, String kind, String from, String to,
                           String method, Map<String, Object> row) {
            this.id = id;
            this.kind = kind;
            this.from = from;
            this.to = to;
            this.method = method;
            this.row = row;
        }

        private void put(String key, Object value) {
            row.put(key, value);
        }

        private void putAll(Map<String, Object> values) {
            row.putAll(values);
        }

        private String value(String key) {
            Object value = row.get(key);
            return value == null || "null".equals(String.valueOf(value))
                    ? "" : String.valueOf(value);
        }
    }

    private static final class MethodControlFlow {
        private final Body body;
        private final UnitGraph graph;
        private final MHGDominatorsFinder<Unit> dominators;
        private final Map<Unit, Fact> factsByUnit;

        private MethodControlFlow(Body body, UnitGraph graph,
                                  Map<Unit, Fact> factsByUnit) {
            this.body = body;
            this.graph = graph;
            this.dominators = new MHGDominatorsFinder<>(graph);
            this.factsByUnit = factsByUnit;
        }
    }

    private static MethodSig parseMethodSig(String raw) {
        if (raw == null || !raw.startsWith("<")) {
            return null;
        }
        Matcher matcher = METHOD_SIGNATURE_PATTERN.matcher(raw);
        if (!matcher.find()) {
            return null;
        }
        String paramsText = matcher.group(4).trim();
        List<String> params = paramsText.isEmpty()
                ? Collections.emptyList()
                : Arrays.asList(paramsText.split("\\s*,\\s*"));
        return new MethodSig(raw, matcher.group(1), matcher.group(2),
                matcher.group(3), params);
    }

    private static String stableSiteId(String method, int unitIndex, String kind) {
        if (unitIndex >= 0) {
            return method + "#u" + unitIndex;
        }
        return method + "#synthetic:" + firstNonBlank(kind, "edge");
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return null;
    }

    private static Map<String, Object> object(Object... keyValues) {
        Map<String, Object> map = new LinkedHashMap<>();
        for (int i = 0; i + 1 < keyValues.length; i += 2) {
            map.put(String.valueOf(keyValues[i]), keyValues[i + 1]);
        }
        return map;
    }
}
