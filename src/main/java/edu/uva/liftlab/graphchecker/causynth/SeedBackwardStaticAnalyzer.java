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
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.BriefUnitGraph;
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
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ExceptionGuard;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.Fact;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.FieldWrite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.MethodCallsite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.actualInvokeArgs;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.fieldOwner;


/** Static backward data-flow analysis from one annotated exception target. */
final class SeedBackwardStaticAnalyzer {
    private static final Logger LOG = LoggerFactory.getLogger(
            CausynthPipeline.class);
    /*
     * Candidate discovery is deliberately cheap and over-approximating.
     * Jimple already lowers a.b.c into receiver locals, so the worklist
     * follows those ordinary def-use facts instead of manufacturing an
     * access-path state. Exact receiver identities and REGION.IN ports are
     * recovered only after runtime region selection.
     */
    private static final int DEFAULT_MAX_METHODS = Integer.MAX_VALUE;
    private static final int MAX_RPC_TARGETS_PER_CALL = Integer.MAX_VALUE;
    private static final int MAX_DISPATCH_TARGETS_PER_CALL =
            Integer.MAX_VALUE;
    private static final int MAX_RUNTIME_RECURSIVE_METHODS =
            Integer.MAX_VALUE;
    private static final int MAX_CONSTRUCTOR_CALLERS_PER_PARAM =
            Integer.MAX_VALUE;
    private static final int MAX_METHOD_CALLERS_PER_METHOD =
            Integer.MAX_VALUE;
    private static final int MAX_FIELD_WRITERS_PER_FIELD =
            Integer.MAX_VALUE;
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
    private static final Pattern METHOD_PARAMETER_SEPARATOR_PATTERN =
            Pattern.compile("\\s*,\\s*");
    private static final Pattern METHOD_THIS_PATTERN = Pattern.compile(
            "([$]?[A-Za-z_][A-Za-z0-9_]*)\\s*:=\\s*@this:");
    private static final Pattern PARAMETER_VALUE_PATTERN = Pattern.compile(
            "@parameter(\\d+):\\s*(.+)");
    private static final Pattern PARAMETER_REFERENCE_PATTERN =
            Pattern.compile("@parameter(\\d+)");
    private static final Pattern NUMERIC_LITERAL_PATTERN = Pattern.compile(
            "-?\\d+(?:[lLfFdD])?");
    private static final Pattern INTEGER_LITERAL_PATTERN =
            Pattern.compile("-?\\d+");
    private static final Pattern FIELD_NAME_PATTERN = Pattern.compile(
            "<[^:]+:\\s+.+\\s+([^\\s>]+)>");
    private static final Pattern ALLOCATION_PATTERN =
            Pattern.compile("^new\\s+([^\\s]+)$");
    private final CausynthTargetContext target;
    private final int maxMethods;
    private final Map<String, SootClass> classesByName = new LinkedHashMap<>();
    private final Map<String, SootMethod> allMethodsBySignature =
            new LinkedHashMap<>();
    private final Map<String, SootMethod> methodsBySignature = new LinkedHashMap<>();
    private final Map<String, List<SootMethod>> concreteMethodsBySubSignature =
            new LinkedHashMap<>();
    private final Map<String, List<Fact>> factsByMethod = new LinkedHashMap<>();
    private final Map<String, MethodControlFlow> controlFlowByMethod =
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
    private final Set<String> dirtyMethods = new LinkedHashSet<>();
    private final Set<String> selectedMethods = new MethodWorkSet();
    private final Map<EdgeIdentity, StaticEdge> emittedEdgeRows =
            new LinkedHashMap<>();
    private final Set<String> expandedDemands = new LinkedHashSet<>();
    private int discoveredExceptionSeedCount;
    /**
     * One call signature has at most one closed-world, side-effect-free
     * structural field accessor.  Negative resolutions are cached as null;
     * {@link Map#containsKey(Object)} distinguishes them from a cache miss.
     */
    private final Map<String, StructuralFieldAccessor>
            structuralFieldAccessors = new LinkedHashMap<>();
    private final Map<String, MethodSig> methodSignatureCache =
            new LinkedHashMap<>();
    private final Set<String> invalidMethodSignatures =
            new LinkedHashSet<>();
    private final Map<String, String> methodThisNodeCache =
            new LinkedHashMap<>();
    private final Set<String> methodsWithoutThisNode =
            new LinkedHashSet<>();
    private final Map<String, List<String>> dispatchSourcesCache =
            new LinkedHashMap<>();
    private final Map<String, List<String>> dispatchTargetsCache =
            new LinkedHashMap<>();
    private final Map<String, Set<String>> hierarchyNamesCache =
            new LinkedHashMap<>();
    private final Map<Fact, List<String>> localValueUsesCache =
            new IdentityHashMap<>();
    private final Map<Fact, List<String>> nonInvokeUsesCache =
            new IdentityHashMap<>();
    private final Map<Fact, List<String>> canonicalDefsCache =
            new IdentityHashMap<>();
    private final Map<Fact, List<String>> canonicalLocalUsesCache =
            new IdentityHashMap<>();
    private final Map<String, List<ExceptionGuard>> requiredPathGuardsByFact =
            new LinkedHashMap<>();
    private final RuntimeDispatchEvidence runtimeDispatchEvidence;
    private final ConfiguredProtocolStubs protocolStubs;
    private final Set<String> runtimeRecursiveMethods =
            new LinkedHashSet<>();
    private final List<StaticEdge> edges = new ArrayList<>();
    private boolean globalStaticIndexBuilt;
    private int edgeCounter;

    SeedBackwardStaticAnalyzer(CausynthTargetContext target) {
        this.target = target;
        this.maxMethods = DEFAULT_MAX_METHODS;
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
                allMethodsBySignature.put(method.getSignature(), method);
                if (method.isConcrete()) {
                    methodsBySignature.put(method.getSignature(), method);
                    concreteMethodsBySubSignature
                            .computeIfAbsent(method.getSubSignature(),
                                    ignored -> new ArrayList<>())
                            .add(method);
                }
            }
        }
        try {
            this.protocolStubs = ConfiguredProtocolStubs.fromConfiguration(
                    allMethodsBySignature);
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load configured protocol stubs", exception);
        }
    }

    private boolean classImplementsOrExtends(SootClass candidate, String targetClassName) {
        return candidate != null && targetClassName != null
                && hierarchyNames(candidate).contains(targetClassName);
    }

    private Set<String> hierarchyNames(SootClass root) {
        Set<String> cached = hierarchyNamesCache.get(root.getName());
        if (cached != null) {
            return cached;
        }
        Set<String> names = new LinkedHashSet<>();
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
                names.add(sootClass.getName());
                if (sootClass.hasSuperclass()) {
                    work.addFirst(sootClass.getSuperclass());
                }
                for (SootClass iface : sootClass.getInterfaces()) {
                    work.addLast(iface);
                }
            } catch (RuntimeException ignored) {
                break;
            }
        }
        Set<String> result = Collections.unmodifiableSet(names);
        hierarchyNamesCache.put(root.getName(), result);
        return result;
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
        String targetMethod = target.exceptionTargetSite.methodSignature;
        SootMethod sootTarget = methodsBySignature.get(targetMethod);
        if (sootTarget == null || !loadMethod(sootTarget)) {
            throw new IllegalStateException(
                    "Could not load annotated target method: "
                            + targetMethod);
        }
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
        result.targetResolved.put("candidateDiscoveryMode",
                "CHEAP_RECEIVER_DEF_USE_JUMP_V1");
        result.targetResolved.put("regionInputAnalysis",
                "DEFERRED_UNTIL_RUNTIME_REGION_SELECTION");
        result.targetResolved.put("accessPathWorklistState", false);
        result.targetResolved.put("receiverDefUseEnabled", true);
        result.targetResolved.put("globalFieldWriterIndexSize",
                fieldWritersByField.size());
        result.targetResolved.put("globalMethodCallerIndexSize",
                methodCallersByCallee.size());
        result.targetResolved.put("globalConstructorCallerIndexSize",
                constructorCallersByCallee.size());
        result.targetResolved.put("recursiveReceiverEffectClosure", false);
        result.targetResolved.put("emittedEdgeCount", result.edges.size());
        result.targetResolved.put("selectedMethodCount",
                result.traceMethods.size());
        return result;
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
        List<Fact> facts = factsFromBody(method.getSignature(), body);
        factsByMethod.put(method.getSignature(), facts);
        methodsBySignature.put(method.getSignature(), method);
        return true;
    }

    private void initializeExceptionSeedAnchors() {
        String method = target.exceptionTargetSite.methodSignature;
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null) {
            throw new IllegalStateException(
                    "Annotated target has no loaded Jimple body: " + method);
        }
        for (int throwIndex = 0; throwIndex < facts.size(); throwIndex++) {
            Fact throwFact = facts.get(throwIndex);
            if (annotatedExceptionAllocation(facts,
                    throwIndex) == null) {
                continue;
            }

            String exceptionNode = factNode(throwFact) + "#exception:"
                    + target.seedException;
            Set<String> methodRelevant = relevant(method);
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
        LOG.info("Discovered {} direct throw sites for {} in {} methods",
                discoveredExceptionSeedCount, target.seedException,
                discoveredExceptionSeedCount == 0 ? 0 : 1);
    }

    private Fact annotatedExceptionAllocation(
            List<Fact> facts, int throwIndex) {
        Fact fact = facts.get(throwIndex);
        if (!(fact.unit instanceof ThrowStmt)) {
            return null;
        }
        ThrowStmt stmt = (ThrowStmt) fact.unit;
        Fact allocation = findExceptionAllocation(facts,
                throwIndex, stmt.getOp().toString());
        if (allocation == null) {
            return null;
        }
        int ordinal = 0;
        for (Fact candidate : facts) {
            if (!target.seedException.equals(
                    allocatedExceptionType(candidate))) {
                continue;
            }
            if (candidate == allocation) {
                return ordinal == target.exceptionTargetSite
                        .exceptionConstructionOrdinal ? allocation : null;
            }
            ordinal++;
        }
        return null;
    }

    private Fact findExceptionAllocation(List<Fact> facts, int throwIndex,
                                         String thrownValue) {
        Set<String> work = new LinkedHashSet<>();
        String initial = localName(thrownValue);
        if (initial != null) {
            work.add(initial);
        }
        for (int i = throwIndex - 1; i >= 0 && !work.isEmpty(); i--) {
            Fact fact = facts.get(i);
            Set<String> defs = localNames(fact.defs);
            if (!intersectsLocal(work, defs)) {
                continue;
            }
            if (target.seedException.equals(allocatedExceptionType(fact))) {
                return fact;
            }
            work.removeAll(defs);
            work.addAll(localNames(nonInvokeUses(fact)));
        }
        return null;
    }

    private String allocatedExceptionType(Fact fact) {
        if (fact == null || !(fact.unit instanceof AssignStmt)) {
            return "";
        }
        Value value = ((AssignStmt) fact.unit).getRightOp();
        return value instanceof NewExpr
                ? ((NewExpr) value).getBaseType().getClassName() : "";
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
        List<ExceptionGuard> guards = new ArrayList<>();
        for (Fact candidate : factsByMethod.getOrDefault(method,
                Collections.emptyList())) {
            if (!candidate.isBranch) {
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
            // Control dependence does not require the branch itself to
            // dominate the target.  In javac's lowering of `a && b || c`,
            // an earlier short-circuit branch may be bypassed by another
            // operand while still deciding whether a relevant definition is
            // reached.  Requiring dominance dropped precisely those guards.
            // The successor test is the actual bounded criterion: for an
            // ordinary output definition, at least one but not every
            // successor reaches it without revisiting the branch.
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
        // Monotone fixed point over finite Jimple cells, declared fields and
        // indexed activation edges. No access path is part of worklist state.
        while (!dirtyMethods.isEmpty()) {
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
            expandMethodActivations(method);
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
            List<String> defs = canonicalDefs(method, fact);
            List<String> uses = canonicalLocalValueUses(method, fact);
            if (fact.isReturn) {
                defs = new ArrayList<>(defs);
                defs.add(method + ".return");
            }
            if (fact.unitText.contains("@parameter") && methodSig != null) {
                uses = new ArrayList<>(uses);
                uses.addAll(parameterNodesFromUnit(methodSig, fact.unitText));
            }

            boolean defExactHit = exactIntersects(relevant, defs);
            boolean defHit = defExactHit;
            boolean useExactHit = exactIntersects(relevant, uses);
            if (defHit) {
                for (String def : defs) {
                    for (String use : uses) {
                        if (ignoreNode(def) || ignoreNode(use)) {
                            continue;
                        }
                        addEdge("local_def_use", use, def, method, fact,
                                "Jimple use/field/argument flows to def");
                    }
                }
                for (String use : uses) {
                    relevant.add(use);
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
            if (!defExactHit) {
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
            relevant.add(fieldNode);
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
        EdgeIdentity key = edgeKey("heap_mutation_path_guard", guardNode,
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
            relevant.add(source);
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
                        || selectedMethods.size() >= maxMethods) {
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
                    writerRelevant.add(source);
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
        boolean thisRelevant = thisNode != null
                && relevant(method).contains(thisNode);
        if (params.isEmpty() && !thisRelevant) {
            return;
        }
        buildGlobalStaticIndex();
        Set<String> constructorsToExpand = new LinkedHashSet<>();
        for (ConstructorParam param : params) {
            constructorsToExpand.add(param.constructor);
        }
        if (thisRelevant) {
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
                            callsite);
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
                        || count++ >= MAX_CONSTRUCTOR_CALLERS_PER_PARAM) {
                    break;
                }
                if (param.index >= callsite.actuals.size()) {
                    continue;
                }
                String actual = callsite.actuals.get(param.index);
                if (ignoreNode(actual)) {
                    MethodSig constructor = parseMethodSig(
                            param.constructor);
                    addTypedLiteralCallerArgument(
                            "constructor_caller_literal_argument",
                            constructor, param.index, callsite.method,
                            callsite.fact);
                    if (constructor != null
                            && param.index < constructor.params.size()
                            && isTypedLiteralArgument(callsite.fact,
                            param.index,
                            constructor.params.get(param.index))) {
                        selectedMethods.add(callsite.method);
                    }
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
        boolean thisRelevant = thisNode != null
                && calleeRelevant.contains(thisNode);
        List<Integer> relevantParams = new ArrayList<>();
        for (int i = 0; i < callee.params.size(); i++) {
            String formal = formalParam(callee, i);
            if (calleeRelevant.contains(formal)) {
                relevantParams.add(i);
            }
        }
        if (relevantParams.isEmpty() && !thisRelevant) {
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
                    || selectedMethods.size() >= maxMethods) {
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
                    addTypedLiteralCallerArgument(
                            "method_caller_literal_argument", callee,
                            index, callsite.method, callsite.fact);
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
                expandCallerReceiver(false, method, thisNode, callsite);
            }
        }
    }

    /**
     * Lifts every selected causal method to its possible invocation sites.
     * This is the cheap component-discovery half of event chaining: it does
     * not require a parameter to be relevant and it does not reconstruct a
     * feasible call path. The reverse-call index makes each callsite visit
     * constant-time after the one-time global scan.
     */
    private void expandMethodActivations(String method) {
        if (!expandOnce("METHOD_ACTIVATIONS", method)) {
            return;
        }
        MethodSig signature = parseMethodSig(method);
        if (signature == null || "<clinit>".equals(signature.name)
                || !isApplicationClassName(signature.owner)) {
            return;
        }
        buildGlobalStaticIndex();
        if ("<init>".equals(signature.name)) {
            for (ConstructorCallsite callsite : constructorCallersByCallee
                    .getOrDefault(method, Collections.emptyList())) {
                selectActivationCaller("constructor_activation", method,
                        callsite.method, callsite.fact);
            }
            return;
        }
        for (MethodCallsite callsite : methodCallersByCallee.getOrDefault(
                method, Collections.emptyList())) {
            selectActivationCaller("method_activation", method,
                    callsite.method, callsite.fact);
        }
    }

    private void selectActivationCaller(String kind, String targetMethod,
                                        String callerMethod, Fact callsite) {
        if (callerMethod == null || callsite == null
                || !expandOnce(kind, targetMethod, callerMethod,
                callsite.unitIndex)) {
            return;
        }
        SootMethod caller = methodsBySignature.get(callerMethod);
        if (caller != null) {
            loadMethod(caller);
        }
        String activation = targetMethod + ".activation";
        addEdge(kind, factNode(callsite), activation, callerMethod, callsite,
                "indexed callsite may activate selected causal method");
        selectedMethods.add(callerMethod);

        for (ExceptionGuard guard : controllingGuards(callerMethod,
                callsite)) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(callerMethod, use);
                if (ignoreNode(guardNode)) {
                    continue;
                }
                addEdge("activation_path_guard", guardNode, activation,
                        callerMethod, guard.fact,
                        "dominating branch controls indexed activation at u"
                                + callsite.unitIndex);
                relevant(callerMethod).add(guardNode);
            }
        }
    }

    private void addTypedLiteralCallerArgument(
            String kind, MethodSig callee, int argumentIndex,
            String callerMethod, Fact fact) {
        Value literal = invokeArgument(fact, argumentIndex);
        if (callee == null || !(literal instanceof Constant)
                || argumentIndex < 0
                || argumentIndex >= callee.params.size()) {
            return;
        }
        String formalType = callee.params.get(argumentIndex);
        String literalValue = typedLiteralValue(literal, formalType);
        if (literalValue.isEmpty()) {
            return;
        }
        String source = factNode(fact);
        String target = formalParam(callee, argumentIndex);
        addEdge(kind, source, target, callerMethod, fact,
                "exact callsite supplies a typed literal to relevant callee formal");
        StaticEdge edge = emittedEdgeRows.get(edgeKey(kind, source, target,
                callerMethod, fact));
        if (edge != null) {
            edge.put("argumentIndex", argumentIndex);
            edge.put("literalType", formalType);
            edge.put("literalValue", literalValue);
        }
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
        return factsFromBody(method.getSignature(), body);
    }

    private List<Fact> factsFromBody(String method, Body body) {
        List<Fact> facts = new ArrayList<>();
        int index = 0;
        for (Unit unit : body.getUnits()) {
            facts.add(new Fact(method, index++, unit));
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
                        canonicalDefs(method, fact)));
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
            if (!formalExact) {
                continue;
            }
            relevantFlow = true;
            addEdge(kind, actual, formal, callerMethod, fact, evidence);
            if (formalExact) {
                callerRelevant.add(actual);
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
            boolean callerHit = callerRelevant.contains(def);
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
            if (!ignoreNode(def) && callerRelevant.contains(def)) {
                relevantDefs.add(def);
            }
        }
        if (relevantDefs.isEmpty()) return;

        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) return;
        String receiverNode = canonical(callerMethod, receiver);
        if (ignoreNode(receiverNode)) return;
        for (String def : relevantDefs) {
            addEdge("container_projection", receiverNode, def,
                    callerMethod, fact,
                    "modeled Java container result depends on receiver state");
        }
        callerRelevant.add(receiverNode);

        for (String argument : canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText))) {
            if (ignoreNode(argument)) continue;
            for (String def : relevantDefs) {
                addEdge("container_argument", argument, def,
                        callerMethod, fact,
                        "modeled Java container result depends on argument");
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

    /** Returns the canonical local bound to {@code @this}. */
    private String methodThisNode(String method, List<Fact> facts) {
        String cached = methodThisNodeCache.get(method);
        if (cached != null) {
            return cached;
        }
        if (methodsWithoutThisNode.contains(method)) {
            return null;
        }
        for (Fact fact : facts) {
            Matcher matcher = METHOD_THIS_PATTERN.matcher(fact.unitText);
            if (matcher.find()) {
                String result = canonical(method, matcher.group(1));
                methodThisNodeCache.put(method, result);
                return result;
            }
        }
        methodsWithoutThisNode.add(method);
        return null;
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
        String receiverNode = canonical(callerMethod, receiver);
        if (ignoreNode(receiverNode)) {
            return;
        }
        String fieldType = declaredField.getType().toString();
        if (fieldType.isEmpty()
                || !erasedTypeName(fieldType).equals(
                erasedTypeName(callee.returnType))) {
            return;
        }
        boolean defExactHit = exactIntersects(callerRelevant, defs);
        if (!defExactHit) {
            return;
        }
        String declaredFieldNode = declaredField.getSignature();
        for (String def : defs) {
            if (ignoreNode(def)) {
                continue;
            }
            addEdge("accessor_field_return", declaredFieldNode, def,
                    callerMethod, fact,
                    "accessor return reads canonical declared field");
            annotateAccessorDeclaredFieldEdge(declaredFieldNode, def,
                    callerMethod, fact, declaredField,
                    accessor.implementation);
            addEdge("accessor_receiver", receiverNode, def,
                    callerMethod, fact,
                    "accessor receiver identifies the object supplying the field");
        }
        callerRelevant.add(receiverNode);
        callerRelevant.add(declaredFieldNode);
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

    private String fieldNameFromSignature(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = FIELD_NAME_PATTERN.matcher(fieldSignature);
        return matcher.matches() ? matcher.group(1) : "";
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
        List<ProtocolStubMapping> mappings =
                protocolStubs.targets(callee.raw);
        if (mappings.isEmpty()) {
            return;
        }
        int count = 0;
        for (ProtocolStubMapping mapping : mappings) {
            String target = mapping.serverStub;
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
            propagateProtocolArguments(mapping, "rpc_argument",
                    callerMethod, fact, target, targetSig, actuals,
                    callerRelevant, targetRelevant);
            if (mapping.response) {
                propagateProtocolReturn(mapping, "rpc_return",
                        callerMethod, fact, target, defs, callerRelevant,
                        targetRelevant, false);
            }
        }
    }

    private boolean propagateProtocolArguments(
            ProtocolStubMapping mapping, String kind, String callerMethod,
            Fact fact, String targetMethod, MethodSig target,
            List<String> actuals, Set<String> callerRelevant,
            Set<String> targetRelevant) {
        boolean relevantFlow = false;
        for (ProtocolPortMapping port : mapping.request) {
            String actual = protocolProjection(
                    actuals.get(port.clientArgument),
                    port.clientProjection);
            if (ignoreNode(actual)) {
                continue;
            }
            String formal = formalParam(target, port.serverParameter);
            boolean formalExact = targetRelevant.contains(formal);
            if (!formalExact) {
                continue;
            }
            relevantFlow = true;
            addProtocolEdge(kind, actual, formal, callerMethod, fact,
                    "configured protocol request flows to server formal",
                    mapping, port.name);
            if (formalExact) {
                callerRelevant.add(actual);
            }
        }
        return relevantFlow;
    }

    private void propagateProtocolReturn(
            ProtocolStubMapping mapping, String kind, String callerMethod,
            Fact fact, String targetMethod, List<String> defs,
            Set<String> callerRelevant, Set<String> targetRelevant,
            boolean forceExpansion) {
        String returnNode = targetMethod + ".return";
        for (String def : defs) {
            boolean callerHit = callerRelevant.contains(def);
            if (!callerHit && !forceExpansion) {
                continue;
            }
            addProtocolEdge(kind, returnNode, def, callerMethod, fact,
                    "configured protocol response flows to caller",
                    mapping, "response");
            if (callerHit || forceExpansion) {
                targetRelevant.add(returnNode);
                selectedMethods.add(targetMethod);
            }
            if (forceExpansion) {
                callerRelevant.add(def);
            }
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
            boolean callRelevant = exactIntersects(callerRelevant, defs);
            callRelevant |= propagateCallArguments("dispatch_argument",
                    "interface/virtual dispatch actual flows to concrete formal",
                    callerMethod, fact, targetMethod, targetSig, actuals,
                    callerRelevant, targetRelevant, true);
            propagateCallReturns("dispatch_return",
                    "concrete dispatch return flows to caller",
                    callerMethod, fact, targetMethod, defs,
                    callerRelevant, targetRelevant, true,
                    false);
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
                || protocolStubs.isClientOwner(callee.owner)) {
            return Collections.emptyList();
        }
        List<String> cached = dispatchTargetsCache.get(callee.raw);
        if (cached != null) {
            return cached;
        }
        SootClass owner = classesByName.get(callee.owner);
        if (owner == null || (!owner.isInterface() && !owner.isAbstract())) {
            dispatchTargetsCache.put(callee.raw, Collections.emptyList());
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
            dispatchTargetsCache.put(callee.raw, Collections.emptyList());
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
        List<String> result = targets.isEmpty()
                ? Collections.emptyList()
                : Collections.unmodifiableList(targets);
        dispatchTargetsCache.put(callee.raw, result);
        return result;
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

    private void expandRpcCallers(String targetMethod) {
        List<ProtocolStubMapping> mappings =
                protocolStubs.sources(targetMethod);
        if (mappings.isEmpty()) {
            return;
        }
        MethodSig targetSig = parseMethodSig(targetMethod);
        if (targetSig == null) {
            return;
        }
        Set<String> targetRelevant = relevant(targetMethod);
        buildGlobalStaticIndex();
        int mappingCount = 0;
        for (ProtocolStubMapping mapping : mappings) {
            if (mappingCount++ >= MAX_RPC_TARGETS_PER_CALL) {
                break;
            }
            List<MethodCallsite> callsites =
                    methodCallersByCallee.get(mapping.clientStub);
            if (callsites == null) {
                continue;
            }
            for (MethodCallsite callsite : callsites) {
                if (selectedMethods.size() >= maxMethods) {
                    break;
                }
                SootMethod callerMethod =
                        methodsBySignature.get(callsite.method);
                if (callerMethod != null) {
                    loadMethod(callerMethod);
                }
                selectActivationCaller("rpc_activation", targetMethod,
                        callsite.method, callsite.fact);
                Set<String> callerRelevant = relevant(callsite.method);
                expandProtocolCallerArguments(mapping, targetMethod,
                        targetSig, targetRelevant, callsite,
                        callerRelevant);
            }
        }
    }

    private void expandProtocolCallerArguments(
            ProtocolStubMapping mapping, String targetMethod,
            MethodSig target, Set<String> targetRelevant,
            MethodCallsite callsite, Set<String> callerRelevant) {
        for (ProtocolPortMapping port : mapping.request) {
            String formal = formalParam(target, port.serverParameter);
            if (!targetRelevant.contains(formal)
                    || !expandOnce("RPC_CALLER_PARAM", targetMethod,
                    mapping.clientStub, port.clientArgument,
                    port.serverParameter, callsite.method,
                    callsite.fact.unitIndex)) {
                continue;
            }
            String actual = protocolProjection(
                    callsite.actuals.get(port.clientArgument),
                    port.clientProjection);
            if (ignoreNode(actual)) {
                continue;
            }
            addProtocolEdge("rpc_caller_argument", actual, formal,
                    callsite.method, callsite.fact,
                    "configured protocol caller actual reaches "
                            + "server formal",
                    mapping, port.name);
            callerRelevant.add(actual);
            selectedMethods.add(callsite.method);
        }
    }

    private String protocolProjection(String base, String projection) {
        // Keep the request object as the cheap static dependency. Runtime
        // evidence resolves any configured message-field projection after
        // the participating client/server activations are known.
        return base;
    }

    private void expandDispatchCallers(String targetMethod) {
        List<String> sourceMethods = resolveDispatchSources(targetMethod);
        if (sourceMethods == null || sourceMethods.isEmpty()) {
            return;
        }
        MethodSig targetSig = parseMethodSig(targetMethod);
        if (targetSig == null) {
            return;
        }
        Set<String> targetRelevant = relevant(targetMethod);
        String targetThis = methodThisNode(targetMethod);
        boolean targetThisRelevant = targetThis != null
                && targetRelevant.contains(targetThis);
        buildGlobalStaticIndex();
        for (String sourceMethod : sourceMethods) {
            List<MethodCallsite> callsites = methodCallersByCallee.get(sourceMethod);
            if (callsites == null) {
                continue;
            }
            for (MethodCallsite callsite : callsites) {
                if (selectedMethods.size() >= maxMethods
                        && !runtimeRecursiveMethods.contains(targetMethod)) {
                    break;
                }
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
                SootMethod callerMethod = methodsBySignature.get(callsite.method);
                if (callerMethod != null) {
                    loadMethod(callerMethod);
                }
                selectActivationCaller("dispatch_activation", targetMethod,
                        callsite.method, callsite.fact);
                Set<String> callerRelevant = relevant(callsite.method);
                expandCallerArguments("DISPATCH_CALLER_PARAM",
                        "dispatch_caller_argument",
                        "interface/virtual caller actual reaches concrete formal",
                        targetMethod, sourceMethod, targetSig, targetRelevant,
                        callsite, callerRelevant);
                if (targetThisRelevant) {
                    expandCallerReceiver(true, targetMethod,
                            targetThis, callsite);
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

    private void expandCallerReceiver(
            boolean dispatch, String targetMethod, String targetThis,
            MethodCallsite callsite) {
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
    }

    private List<String> resolveDispatchSources(String targetMethod) {
        List<String> cached = dispatchSourcesCache.get(targetMethod);
        if (cached != null) {
            return cached;
        }
        MethodSig targetSig = parseMethodSig(targetMethod);
        if (targetSig == null || skipDispatchOwner(targetSig.owner)) {
            dispatchSourcesCache.put(targetMethod, Collections.emptyList());
            return Collections.emptyList();
        }
        SootClass targetClass = classesByName.get(targetSig.owner);
        if (targetClass == null) {
            dispatchSourcesCache.put(targetMethod, Collections.emptyList());
            return Collections.emptyList();
        }
        Set<String> sources = new LinkedHashSet<>();
        String subSignature = methodSubSignature(targetSig);
        for (String candidateName : hierarchyNames(targetClass)) {
            SootClass candidate = classesByName.get(candidateName);
            if (candidate == null || !candidate.isApplicationClass()
                    || skipDispatchOwner(candidate.getName())
                    || protocolStubs.isClientOwner(candidate.getName())
                    || (!candidate.isInterface() && !candidate.isAbstract())) {
                continue;
            }
            for (SootMethod method : candidate.getMethods()) {
                if (subSignature.equals(method.getSubSignature())) {
                    sources.add(method.getSignature());
                }
            }
        }
        List<String> result = sources.isEmpty()
                ? Collections.emptyList()
                : Collections.unmodifiableList(new ArrayList<>(sources));
        dispatchSourcesCache.put(targetMethod, result);
        return result;
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
            return true;
        }

    }

    private List<String> nonInvokeUses(Fact fact) {
        List<String> cached = nonInvokeUsesCache.get(fact);
        if (cached != null) {
            return cached;
        }
        List<String> uses = new ArrayList<>();
        for (String use : fact.uses) {
            if (!use.startsWith("virtualinvoke ")
                    && !use.startsWith("interfaceinvoke ")
                    && !use.startsWith("specialinvoke ")
                    && !use.startsWith("staticinvoke ")) {
                uses.add(use);
            }
        }
        List<String> result = uses.isEmpty()
                ? Collections.emptyList()
                : Collections.unmodifiableList(uses);
        nonInvokeUsesCache.put(fact, result);
        return result;
    }

    private List<String> localValueUses(Fact fact) {
        List<String> cached = localValueUsesCache.get(fact);
        if (cached != null) {
            return cached;
        }
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
        List<String> result = uses.isEmpty()
                ? Collections.emptyList()
                : Collections.unmodifiableList(new ArrayList<>(uses));
        localValueUsesCache.put(fact, result);
        return result;
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
                || NUMERIC_LITERAL_PATTERN.matcher(trimmed).matches()
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

    private List<String> canonicalDefs(String method, Fact fact) {
        return cachedCanonicalList(canonicalDefsCache, method, fact,
                fact.defs);
    }

    private List<String> canonicalLocalValueUses(String method, Fact fact) {
        return cachedCanonicalList(canonicalLocalUsesCache, method, fact,
                localValueUses(fact));
    }

    private List<String> cachedCanonicalList(
            Map<Fact, List<String>> cache, String method, Fact fact,
            Collection<String> values) {
        List<String> cached = cache.get(fact);
        if (cached != null) {
            return cached;
        }
        List<String> canonical = canonicalList(method, values);
        List<String> result = canonical.isEmpty()
                ? Collections.emptyList()
                : Collections.unmodifiableList(canonical);
        cache.put(fact, result);
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
        Matcher parameter = PARAMETER_VALUE_PATTERN.matcher(trimmed);
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
        if (LOCAL_NAME_PATTERN.matcher(trimmed).matches()) {
            return method + "::" + trimmed;
        }
        return trimmed;
    }

    private List<String> parameterNodesFromUnit(MethodSig sig, String unit) {
        List<String> nodes = new ArrayList<>();
        Matcher matcher = PARAMETER_REFERENCE_PATTERN.matcher(unit);
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
        String cached = methodThisNodeCache.get(method);
        if (cached != null) {
            return cached;
        }
        if (methodsWithoutThisNode.contains(method)) {
            return null;
        }
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null) {
            return null;
        }
        return methodThisNode(method, facts);
    }

    private void expandConstructorReceiverFields(String constructor,
                                                 String constructorThis,
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
    }

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

    private void addEdge(String kind, Object from, Object to, String method,
                         Fact fact, String evidence) {
        addEdgeInternal(kind, from, to, method, fact, evidence);
    }

    private void addProtocolEdge(
            String kind, Object from, Object to, String method, Fact fact,
            String evidence, ProtocolStubMapping mapping, String port) {
        addEdge(kind, from, to, method, fact, evidence);
        StaticEdge edge = emittedEdgeRows.get(
                edgeKey(kind, from, to, method, fact));
        if (edge == null) {
            return;
        }
        edge.put("protocolStubMappingId", mapping.id);
        edge.put("protocolTransport", mapping.transport);
        edge.put("protocolPort", port);
    }

    private void addEdgeInternal(String kind, Object from, Object to,
                                 String method, Fact fact, String evidence) {
        if (from == null || to == null) {
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
        EdgeIdentity key = edgeKey(kind, fromText, toText, method, fact);
        StaticEdge edge = emittedEdgeRows.get(key);
        if (edge == null) {
            String edgeId = "DF." + edgeCounter++;
            String semanticMode = StaticDataflowEdgeSchema.ASSERTABLE;
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
            String relation = exactDirectCopy
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

    private EdgeIdentity edgeKey(String kind, Object from, Object to,
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
        return new EdgeIdentity(String.valueOf(kind), String.valueOf(from),
                String.valueOf(to), String.valueOf(method),
                fact != null, fact == null ? -1 : fact.unitIndex);
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
        Matcher allocation = ALLOCATION_PATTERN.matcher(
                fromCell == null ? "" : fromCell.trim());
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

    private boolean ignoreNode(String value) {
        if (value == null) {
            return true;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty()
                || "null".equals(trimmed)
                || INTEGER_LITERAL_PATTERN.matcher(trimmed).matches()
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

    /**
     * Exact replacement for the old newline-joined edge key.  Keeping the
     * endpoint strings as tuple members avoids retaining a second, much
     * larger concatenated char array for every emitted edge.
     */
    private static final class EdgeIdentity {
        private final String kind;
        private final String from;
        private final String to;
        private final String method;
        private final boolean concreteSite;
        private final int unitIndex;
        private final int hash;

        private EdgeIdentity(String kind, String from, String to,
                             String method, boolean concreteSite,
                             int unitIndex) {
            this.kind = kind;
            this.from = from;
            this.to = to;
            this.method = method;
            this.concreteSite = concreteSite;
            this.unitIndex = unitIndex;
            int value = kind.hashCode();
            value = 31 * value + from.hashCode();
            value = 31 * value + to.hashCode();
            value = 31 * value + method.hashCode();
            value = 31 * value + (concreteSite ? 1 : 0);
            hash = 31 * value + unitIndex;
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (!(other instanceof EdgeIdentity)) {
                return false;
            }
            EdgeIdentity identity = (EdgeIdentity) other;
            return concreteSite == identity.concreteSite
                    && unitIndex == identity.unitIndex
                    && kind.equals(identity.kind)
                    && from.equals(identity.from)
                    && to.equals(identity.to)
                    && method.equals(identity.method);
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
        private final Map<Unit, Fact> factsByUnit;

        private MethodControlFlow(Body body, UnitGraph graph,
                                  Map<Unit, Fact> factsByUnit) {
            this.body = body;
            this.graph = graph;
            this.factsByUnit = factsByUnit;
        }
    }

    private MethodSig parseMethodSig(String raw) {
        if (raw == null || !raw.startsWith("<")) {
            return null;
        }
        MethodSig cached = methodSignatureCache.get(raw);
        if (cached != null) {
            return cached;
        }
        if (invalidMethodSignatures.contains(raw)) {
            return null;
        }
        Matcher matcher = METHOD_SIGNATURE_PATTERN.matcher(raw);
        if (!matcher.find()) {
            invalidMethodSignatures.add(raw);
            return null;
        }
        String paramsText = matcher.group(4).trim();
        List<String> params = paramsText.isEmpty()
                ? Collections.emptyList()
                : Arrays.asList(METHOD_PARAMETER_SEPARATOR_PATTERN.split(
                        paramsText));
        MethodSig result = new MethodSig(raw, matcher.group(1), matcher.group(2),
                matcher.group(3), params);
        methodSignatureCache.put(raw, result);
        return result;
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
