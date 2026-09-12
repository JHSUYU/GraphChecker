package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.annotation.Debug;

import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.SiteId;
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
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThrowStmt;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.Callsite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ConstructorParam;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ArrayAccess;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ExceptionGuard;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.Fact;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.FieldWrite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.InstanceFieldAccess;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.actualInvokeArgs;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.activeBody;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.fieldOwner;
import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;


/** Static backward data-flow analysis from one annotated exception target. */
final class SeedBackwardStaticAnalyzer {
    private static final Logger LOG = LoggerFactory.getLogger(
            CausynthPipeline.class);
    /** Candidate discovery is deliberately cheap and over-approximating. */
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
    /** The nullary unboxing accessors that pass their receiver's value on. */
    private static final Set<String> VALUE_LIKE_UNBOXING = names(
            "java.lang.Byte.byteValue", "java.lang.Short.shortValue",
            "java.lang.Integer.intValue", "java.lang.Long.longValue",
            "java.lang.Character.charValue", "java.lang.Float.floatValue",
            "java.lang.Double.doubleValue");
    /** Java collection APIs whose returned object stays backed by its
     *  receiver, so a mutation of one is a mutation of the other. */
    private static final Set<String> BACKED_MAP_VIEWS = names(
            "entrySet", "keySet", "values", "navigableKeySet",
            "descendingKeySet");
    private static final Set<String> BACKED_ITERATORS = names(
            "iterator", "listIterator", "descendingIterator");
    /** Container calls that write their receiver. */
    private static final Set<String> CONTAINER_MUTATORS = names(
            "put", "putAll", "remove", "clear", "add", "addAll", "set",
            "replace", "compute", "computeIfAbsent", "computeIfPresent",
            "merge", "offer", "poll");
    /** Numeric atomic read-modify-write calls: they mutate the receiver even
     *  though their Jimple call site contains no field assignment. */
    private static final Set<String> ATOMIC_NUMERIC_MUTATIONS = names(
            "getAndIncrement", "getAndDecrement", "getAndAdd",
            "incrementAndGet", "decrementAndGet", "addAndGet", "getAndSet",
            "compareAndSet", "weakCompareAndSet", "lazySet");
    private static final Set<String> MAP_CONTRACT_OWNERS = names(
            "java.util.Map", "java.util.SortedMap", "java.util.NavigableMap",
            "java.util.concurrent.ConcurrentMap",
            "java.util.concurrent.ConcurrentNavigableMap");
    private static final Set<String> COLLECTION_CONTRACT_OWNERS = names(
            "java.util.Collection", "java.util.List", "java.util.Set",
            "java.util.SortedSet", "java.util.NavigableSet",
            "java.util.Queue", "java.util.Deque");
    private final CausynthTargetContext target;
    private final Map<String, SootClass> classesByName = new LinkedHashMap<>();
    private final Map<String, SootMethod> allMethodsBySignature =
            new LinkedHashMap<>();
    private final Map<String, List<SootMethod>> concreteMethodsBySubSignature =
            new LinkedHashMap<>();
    private final Map<String, List<Fact>> factsByMethod = new LinkedHashMap<>();
    private final Map<String, MethodControlFlow> controlFlowByMethod =
            new LinkedHashMap<>();
    private final Map<String, List<FieldWrite>> fieldWritersByField =
            new LinkedHashMap<>();
    private final Map<String, List<Callsite>> constructorCallersByCallee =
            new LinkedHashMap<>();
    private final Map<String, List<Callsite>> methodCallersByCallee =
            new LinkedHashMap<>();
    /** Every application call site of the explicit boolean fault hook. */
    private final Map<String, List<Integer>> explicitFaultUnitsByMethod =
            new LinkedHashMap<>();
    /** Methods whose Jimple mentions one declared field. */
    private final Map<String, Set<String>> methodsReferencingField =
            new LinkedHashMap<>();
    private final Set<String> mutationIndexedFields = new LinkedHashSet<>();
    private final Map<String, Set<String>> relevantFieldEffectsByMethod =
            new LinkedHashMap<>();
    private final Map<String, Set<String>> relevantByMethod = new LinkedHashMap<>();
    private final Set<String> dirtyMethods = new LinkedHashSet<>();
    private final Set<String> selectedMethods =
            new DirtyMarkingSet(null);
    private final Map<EdgeIdentity, Map<String, Object>> emittedEdgeRows =
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
    private final Map<String, Map<Integer, String>>
            directlyMutatedContainerParametersCache = new LinkedHashMap<>();
    private final Map<String, Set<String>> hierarchyNamesCache =
            new LinkedHashMap<>();
    /* Fact, Unit, SootMethod and SootClass all inherit Object.equals, so a
     * LinkedHashMap/LinkedHashSet keeps identity semantics and adds insertion
     * order: no collection on the path to an emitted row iterates in
     * identity-hash order. */
    private final Map<Fact, List<String>> localValueUsesCache =
            new LinkedHashMap<>();
    private final Map<Fact, List<String>> nonInvokeUsesCache =
            new LinkedHashMap<>();
    private final Map<Fact, List<String>> canonicalDefsCache =
            new LinkedHashMap<>();
    private final Map<Fact, List<String>> canonicalLocalUsesCache =
            new LinkedHashMap<>();
    private final Map<String, List<ExceptionGuard>> requiredPathGuardsByFact =
            new LinkedHashMap<>();
    private final WireFlowCatalog wireFlows;
    /** README section 5's per-loop {@code K_L}, as this campaign declares it. */
    private final DeclaredLoopBodyBounds loopBodyBounds;
    private boolean globalStaticIndexBuilt;
    private int edgeCounter;

    SeedBackwardStaticAnalyzer(CausynthTargetContext target) {
        this.target = target;
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            classesByName.put(sootClass.getName(), sootClass);
            for (SootMethod method : sootClass.getMethods()) {
                allMethodsBySignature.put(method.getSignature(), method);
                if (method.isConcrete()) {
                    concreteMethodsBySubSignature
                            .computeIfAbsent(method.getSubSignature(),
                                    ignored -> new ArrayList<>())
                            .add(method);
                }
            }
        }
        try {
            this.wireFlows = WireFlowCatalog.fromConfiguration(
                    allMethodsBySignature);
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load communication mappings", exception);
        }
        try {
            this.loopBodyBounds =
                    DeclaredLoopBodyBounds.fromConfiguration();
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load declared loop body bounds", exception);
        }
    }

    private boolean classImplementsOrExtends(SootClass candidate, String targetClassName) {
        return candidate != null && targetClassName != null
                && hierarchyNames(candidate).contains(targetClassName);
    }

    private Set<String> hierarchyNames(SootClass root) {
        return memoized(hierarchyNamesCache, root.getName(), ignored -> {
            Set<String> names = new LinkedHashSet<>();
            // A visitor that never answers visits the whole hierarchy, and
            // ends on the same Soot resolution error the walk itself ends on.
            walkHierarchy(root, sootClass -> {
                names.add(sootClass.getName());
                return null;
            });
            return Collections.unmodifiableSet(names);
        });
    }

    StaticProgram analyze() throws IOException {
        StaticProgram result = new StaticProgram();
        result.targetResolved.put("schemaVersion", 3);
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
        SootMethod sootTarget = concreteMethod(targetMethod);
        if (sootTarget == null || !loadMethod(sootTarget)) {
            throw new IllegalStateException(
                    "Could not load annotated target method: "
                            + targetMethod);
        }
        // Explicit fault hooks are program inputs in their own right.  They
        // must enter the candidate union even when their return value is not
        // already in the annotated exception's value slice; runtime
        // occurrence evidence later decides which of them belongs to the
        // selected target closure.
        buildGlobalStaticIndex();
        initializeExceptionSeedAnchors();
        seedDeclaredWireFlows();
        seedExplicitFaultEntries();
        runWorklist();
        if (discoveredExceptionSeedCount != 1) {
            throw new IllegalStateException("Annotated exception target did "
                    + "not resolve to exactly one Jimple throw: "
                    + target.exceptionTargetSite.stableIdentity()
                    + "; matches=" + discoveredExceptionSeedCount);
        }
        planCommunicationCatalog(result);

        result.edges.addAll(emittedEdgeRows.values());
        result.traceMethods.addAll(selectedMethods);
        Collections.sort(result.traceMethods);
        for (String method : result.traceMethods) {
            String authority = executionContextAuthority(method);
            if (!authority.isEmpty()) {
                result.executionContextAuthorities.put(method, authority);
            }
        }
        // Stated over the final plan: a declaration matched only after the
        // selected set grew must not be refused against an earlier plan.
        loopBodyBounds.refuseUnclaimed();
        return result;
    }

    /**
     * README Step 1 items 1-3, over the methods the seed walk already
     * selected.
     */
    private void planCommunicationCatalog(StaticProgram result) {
        List<String> selected = new ArrayList<>(selectedMethods);
        Collections.sort(selected);
        CommunicationCatalogPlanner.Result discovered =
                CommunicationCatalogPlanner.plan(selected,
                        this::jimpleBody, wireFlows.flows(),
                        loopBodyBounds);
        // The pass is a pure function of the selected method set, so the
        // rows it publishes replace any earlier ones rather than being
        // appended to them.
        result.communicationCallSites.clear();
        result.retainedLoops.clear();
        result.communicationGaps.clear();
        result.communicationCallSiteCallees.clear();
        result.communicationCallSites.addAll(discovered.callSites);
        result.retainedLoops.addAll(discovered.loops);
        result.communicationGaps.addAll(discovered.gaps);
        result.communicationCallSiteCallees.addAll(
                discovered.callSiteCallees);
    }

    private SootMethod concreteMethod(String signature) {
        SootMethod method = allMethodsBySignature.get(signature);
        return method != null && method.isConcrete() ? method : null;
    }

    /**
     * Resolves one method signature to its Jimple body, loading the method
     * first when the seed walk has not already done so.
     */
    private Body jimpleBody(String signature) {
        MethodControlFlow cached = controlFlowByMethod.get(signature);
        if (cached != null) {
            return cached.cfg.body();
        }
        SootMethod method = concreteMethod(signature);
        return method == null ? null : activeBody(method);
    }

    /**
     * Identifies execution-context entries from Java concurrency contracts.
     */
    private String executionContextAuthority(String signature) {
        if (signature == null || signature.contains(" <init>(")
                || signature.contains(" <clinit>(")) {
            return "";
        }
        SootMethod method = allMethodsBySignature.get(signature);
        if (method == null) {
            return "";
        }
        String name = method.getName();
        if ("main".equals(name) && method.isStatic()
                && method.getParameterCount() == 1
                && "java.lang.String[]".equals(
                method.getParameterType(0).toString())) {
            return "MAIN_ENTRY";
        }
        SootClass owner = method.getDeclaringClass();
        if ("run".equals(name) && method.getParameterCount() == 0
                && classImplementsOrExtends(owner, "java.lang.Runnable")) {
            return classImplementsOrExtends(owner, "java.lang.Thread")
                    ? "THREAD_ENTRY" : "TASK_ENTRY";
        }
        if ("call".equals(name) && method.getParameterCount() == 0
                && classImplementsOrExtends(owner,
                "java.util.concurrent.Callable")) {
            return "TASK_ENTRY";
        }
        if (("compute".equals(name) || "exec".equals(name))
                && method.getParameterCount() == 0
                && classImplementsOrExtends(owner,
                "java.util.concurrent.ForkJoinTask")) {
            return "TASK_ENTRY";
        }
        return "";
    }

    private boolean loadMethod(SootMethod method) {
        if (method == null || !method.isConcrete()
                || factsByMethod.containsKey(method.getSignature())) {
            return false;
        }
        Body body = activeBody(method);
        if (body == null) {
            return false;
        }
        List<Fact> facts = factsFromBody(method.getSignature(), body);
        factsByMethod.put(method.getSignature(), facts);
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
            if (annotatedExceptionAllocation(facts, throwIndex) == null) {
                continue;
            }

            String exceptionNode = factNode(throwFact) + "#exception:"
                    + target.seedException;
            Set<String> methodRelevant = relevant(method);
            String thrown = canonical(method,
                    ((ThrowStmt) throwFact.unit).getOp().toString());
            if (!ignoreNode(thrown)) {
                methodRelevant.add(thrown);
                addEdge("exception_throw", thrown, exceptionNode,
                        method, throwFact);
            }
            // Every branch on at least one path to the exact throw.
            forEachGuardOperand(method, branchGuards(method, throwFact,
                    false), (guard, node) -> {
                methodRelevant.add(node);
                Map<String, Object> edge = addEdge("exception_guard",
                        node, exceptionNode, method, guard.fact);
                if (edge != null) {
                    ControlDependenceEdgeSupport
                            .annotatePathGuard(edge, method,
                                    guard.fact.unitIndex,
                                    throwFact.unitIndex,
                                    throwFact.unitText,
                                    guard.requiredOutcome,
                                    guard.reachingSuccessorIndices,
                                    node, exceptionNode);
                }
            });

            selectedMethods.add(method);
            discoveredExceptionSeedCount++;
        }
        LOG.info("Discovered {} direct throw sites for {} in {} methods",
                discoveredExceptionSeedCount, target.seedException,
                discoveredExceptionSeedCount == 0 ? 0 : 1);
    }

    /**
     * A configured wire flow is already an explicit workload boundary.  Seed
     * both exact captures here; runtime request-flow evidence later decides
     * which dynamic occurrences belong to the target execution.
     */
    private void seedDeclaredWireFlows() {
        for (WireFlowCatalog.WireFlow flow : wireFlows.flows()) {
            SootMethod producerMethod = concreteMethod(flow.producer.method);
            SootMethod consumerMethod = concreteMethod(flow.consumer.method);
            if (producerMethod == null || consumerMethod == null
                    || !ensureLoaded(producerMethod)
                    || !ensureLoaded(consumerMethod)) {
                throw new IllegalStateException(
                        "Could not load wire flow endpoints: " + flow.id);
            }
            Fact producerFact = captureFact(flow.producer);
            Fact consumerFact = captureFact(flow.consumer);
            String producer = captureNode(flow.producer, producerFact);
            String consumer = captureNode(flow.consumer, consumerFact);
            if (producer.isEmpty() || consumer.isEmpty()) {
                throw new IllegalStateException(
                        "Could not resolve wire flow captures: " + flow.id);
            }
            relevant(flow.producer.method).add(producer);
            relevant(flow.consumer.method).add(consumer);
            selectedMethods.add(flow.producer.method);
            selectedMethods.add(flow.consumer.method);
            if (WireFlowCatalog.CaptureSite.CALL_ARGUMENT.equals(
                    flow.producer.kind)) {
                MethodSig callee = parseMethodSig(flow.producer.callee);
                if (callee == null) {
                    throw new IllegalStateException(
                            "Could not resolve wire producer call: "
                                    + flow.id);
                }
                addEdge("wire_capture_argument", producer,
                        formalParam(callee, flow.producer.index),
                        flow.producer.method, producerFact);
            }
            addEdge("wire_handoff", producer, consumer,
                    flow.consumer.method,
                    consumerFact == null ? producerFact : consumerFact);
        }
    }

    /**
     * Makes every explicit fault marker an independent static control root.
     * The destination local is demanded before the ordinary backward
     * worklist runs, so a branch that consumes the marker and any guard that
     * controls whether the marker executes are retained by the same generic
     * control-dependence logic as all other symbolic values.
     */
    private void seedExplicitFaultEntries() {
        List<String> methods = new ArrayList<>(
                explicitFaultUnitsByMethod.keySet());
        Collections.sort(methods);
        for (String method : methods) {
            List<Integer> units = new ArrayList<>(
                    explicitFaultUnitsByMethod.get(method));
            Collections.sort(units);
            for (Integer unitIndex : units) {
                Fact fact = indexedFact(method, unitIndex);
                if (fact == null || !Debug.isBooleanMarkerSignature(
                        fact.invoke)) {
                    continue;
                }
                List<String> destinations = new ArrayList<>(
                        canonicalDefs(method, fact));
                // Java bytecode normally assigns a non-void invocation to a
                // local.  Keep an intentionally ignored marker visible as a
                // candidate site as well; it will simply have no flippable
                // dependent branch at runtime.
                if (destinations.isEmpty()) {
                    destinations.add(factNode(fact));
                }
                String source = fact.invoke + ".return";
                String name = explicitFaultName(fact);
                for (String destination : destinations) {
                    relevant(method).add(destination);
                    Map<String, Object> edge = addEdge(
                            "explicit_symbolic_fault", source,
                            destination, method, fact);
                    annotateExplicitSymbolicFaultEdge(edge, method, fact,
                            name);

                    forEachGuardOperand(method,
                            controllingGuards(method, fact),
                            (guard, guardNode) -> {
                                Map<String, Object> guardEdge = addEdge(
                                        ControlDependenceEdgeSupport
                                                .PATH_GUARD_KIND,
                                        guardNode, destination, method,
                                        guard.fact);
                                if (guardEdge != null) {
                                    ControlDependenceEdgeSupport
                                            .annotatePathGuard(guardEdge,
                                                    method,
                                                    guard.fact.unitIndex,
                                                    fact.unitIndex,
                                                    fact.unitText,
                                                    guard.requiredOutcome,
                                                    guard.reachingSuccessorIndices,
                                                    guardNode, destination);
                                }
                                relevant(method).add(guardNode);
                            });
                }
                selectedMethods.add(method);
            }
        }
    }

    private boolean ensureLoaded(SootMethod method) {
        return method != null
                && (factsByMethod.containsKey(method.getSignature())
                || loadMethod(method));
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
            if (!exactIntersects(work, defs)) {
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
     * successors can reach {@code targetFact}.
     */
    private List<ExceptionGuard> controllingGuards(String method,
                                                   Fact targetFact) {
        return memoized(requiredPathGuardsByFact,
                method + "\n" + targetFact.unitIndex,
                ignored -> branchGuards(method, targetFact, true));
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
                    CausynthBranchShape.from(controlFlow.cfg.body(),
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
                if (canReachWithoutRevisiting(controlFlow.cfg,
                        successors.get(successorIndex), targetFact.unit,
                        candidate.unit)) {
                    reachingSuccessors++;
                    reachingIndices.add(successorIndex);
                }
            }
            // Control dependence does not require the branch itself to
            // dominate the target.
            boolean relevant = reachingSuccessors > 0
                    && (!controllingOnly
                    || reachingSuccessors < successors.size());
            if (!relevant) {
                continue;
            }
            Boolean requiredOutcome = null;
            if (candidate.unit instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) candidate.unit;
                boolean takenReaches = canReachWithoutRevisiting(
                        controlFlow.cfg, ifStmt.getTarget(),
                        targetFact.unit, candidate.unit);
                Unit fallThrough = controlFlow.cfg.body().getUnits()
                        .getSuccOf(candidate.unit);
                boolean fallThroughReaches = fallThrough != null
                        && canReachWithoutRevisiting(controlFlow.cfg,
                        fallThrough, targetFact.unit, candidate.unit);
                if (takenReaches != fallThroughReaches) {
                    requiredOutcome = takenReaches;
                }
            }
            guards.add(new ExceptionGuard(candidate, requiredOutcome,
                    reachingIndices));
        }
        guards.sort(Comparator.comparingInt(guard -> guard.fact.unitIndex));
        return Collections.unmodifiableList(guards);
    }

    private MethodControlFlow controlFlow(String method) {
        if (controlFlowByMethod.containsKey(method)) {
            return controlFlowByMethod.get(method);
        }
        SootMethod sootMethod = concreteMethod(method);
        if (sootMethod == null) {
            return null;
        }
        try {
            MethodControlFlow controlFlow = new MethodControlFlow(
                    CfgLoopControl.loopCfg(activeBody(sootMethod)));
            controlFlowByMethod.put(method, controlFlow);
            return controlFlow;
        } catch (RuntimeException ignored) {
            return null;
        }
    }

    /**
     * Tests reachability within the current dynamic occurrence of a candidate
     * branch.
     */
    private boolean canReachWithoutRevisiting(CfgLoopControl.LoopCfg cfg,
                                              Unit start, Unit targetUnit,
                                              Unit candidateBranch) {
        Set<Unit> seen = new LinkedHashSet<>();
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
            work.addAll(cfg.succsOf(current));
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
        // explicit message/dispatch boundaries.
        while (!dirtyMethods.isEmpty()) {
            String method = dirtyMethods.iterator().next();
            dirtyMethods.remove(method);
            if (!selectedMethods.contains(method)) {
                continue;
            }
            processMethod(method);
            expandDispatchCallers(method);
            expandFieldWriters(method);
            expandConstructorCallers(method);
            expandMethodCallers(method);
        }
    }

    private void processMethod(String method) {
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null) {
            return;
        }
        Set<String> relevant = relevant(method);
        MethodSig methodSig = parseMethodSig(method);
        // This is a backward slice.
        for (int factIndex = facts.size() - 1; factIndex >= 0; factIndex--) {
            Fact fact = facts.get(factIndex);
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
                        addEdge("local_def_use", use, def, method, fact);
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
                            method, fact);
                }
            }
            if (fact.isThrow && useExactHit) {
                for (String use : uses) {
                    addEdge("throw_dependency", use, factNode(fact),
                            method, fact);
                }
            }
            processFieldReads(method, fact, defs, relevant);
            processFieldWrites(method, facts, fact, relevant);
            processArrayAccesses(method, fact, defs, relevant);
            processInvoke(method, fact, defs, relevant);
        }
    }

    /**
     * Adds intraprocedural control dependencies for a statement that defines
     * an exactly relevant value.
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

        forEachGuardOperand(method, controllingGuards(method, targetFact),
                (guard, guardNode) -> {
            for (String def : relevantDefs) {
                Map<String, Object> edge = addEdge(
                        ControlDependenceEdgeSupport.PATH_GUARD_KIND,
                        guardNode, def, method, guard.fact);
                if (edge != null) {
                    ControlDependenceEdgeSupport.annotatePathGuard(
                            edge, method, guard.fact.unitIndex,
                            targetFact.unitIndex,
                            targetFact.unitText,
                            guard.requiredOutcome,
                            guard.reachingSuccessorIndices,
                            guardNode, def);
                }
            }
            relevant.add(guardNode);
        });
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
                annotateDirectDeclaredFieldEdge(addEdge("field_read",
                        fieldNode, def, method, fact), field);
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
                    fieldWriteSources(method, fact, field), "field_write");
        }
        for (String mutatedField : fieldsMutatedByInvoke(facts, fact.unitIndex)) {
            String mutatedFieldNode = canonical(method, mutatedField);
            boolean mutationAffectsRelevantState =
                    relevant.contains(mutatedFieldNode);
            processFieldWrite(method, fact, relevant, mutatedField,
                    fieldMutationSources(method, fact, mutatedField),
                    "field_mutation");
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
     * Keeps array contents in the backward slice without turning the array
     * index into a symbolic value.
     */
    private void processArrayAccesses(String method, Fact fact,
                                      List<String> defs,
                                      Set<String> relevant) {
        if (fact.arrayUse != null) {
            processArrayLoad(method, fact, fact.arrayUse, defs, relevant);
        }
        if (fact.arrayDef != null) {
            processArrayStore(method, fact, fact.arrayDef, relevant);
        }
    }

    private void processArrayLoad(String method, Fact fact,
                                  ArrayAccess access, List<String> defs,
                                  Set<String> relevant) {
        List<String> demandedDefs = new ArrayList<>();
        for (String def : defs) {
            if (relevant.contains(def) && !ignoreNode(def)) {
                demandedDefs.add(def);
            }
        }
        if (demandedDefs.isEmpty()) {
            return;
        }
        String base = canonical(method, access.base);
        if (ignoreNode(base)) {
            return;
        }
        String element = arrayElementCell(base);
        addEdge("container_array_load_base", base, element, method, fact);
        relevant.add(base);
        relevant.add(element);
        for (String def : demandedDefs) {
            addEdge("container_array_load_value", element, def,
                    method, fact);
        }
    }

    private void processArrayStore(String method, Fact fact,
                                   ArrayAccess access,
                                   Set<String> relevant) {
        String base = canonical(method, access.base);
        if (ignoreNode(base)) {
            return;
        }
        String element = arrayElementCell(base);
        if (!relevant.contains(base) && !relevant.contains(element)) {
            return;
        }
        addEdge("container_array_store_base", element, base, method, fact);
        relevant.add(element);
        for (String source : arrayStoreSources(method, fact)) {
            if (ignoreNode(source)) {
                continue;
            }
            addEdge("container_array_store_value", source, element,
                    method, fact);
            relevant.add(source);
        }
    }

    private List<String> arrayStoreSources(String method, Fact fact) {
        if (!(fact.unit instanceof DefinitionStmt)) {
            return Collections.emptyList();
        }
        Value value = ((DefinitionStmt) fact.unit).getRightOp();
        Set<String> raw = new LinkedHashSet<>();
        if (atomicDataflowUse(value.toString())) {
            raw.add(value.toString());
        }
        for (soot.ValueBox box : value.getUseBoxes()) {
            String use = box.getValue().toString();
            if (atomicDataflowUse(use)) {
                raw.add(use);
            }
        }
        // FieldRef rendering contains the receiver expression.
        raw.removeIf(this::isFieldAccessValue);
        raw.addAll(fact.fieldUses);
        return canonicalList(method, raw);
    }

    private String arrayElementCell(String canonicalBase) {
        return canonicalBase + "#array-element";
    }

    /**
     * A heap write may have no exactly relevant Jimple definition local, so
     * the ordinary {@link #processRequiredPathGuards(String, Fact, List, Set)}
     * path cannot reliably attach the branches that make the write execute.
     */
    private void processHeapMutationPathGuards(
            String method, Fact mutation, String mutatedCell,
            Set<String> relevant) {
        if (ignoreNode(mutatedCell)) {
            return;
        }
        forEachGuardOperand(method, controllingGuards(method, mutation),
                (guard, guardNode) -> {
            addHeapMutationPathGuardEdge(guardNode, mutatedCell, method,
                    guard, mutation);
            relevant.add(guardNode);
        });
    }

    private void addHeapMutationPathGuardEdge(
            String guardNode, String mutatedCell, String method,
            ExceptionGuard guard, Fact mutation) {
        Map<String, Object> edge = addEdge("heap_mutation_path_guard",
                guardNode, mutatedCell, method, guard.fact);
        if (edge == null) {
            return;
        }
        ControlDependenceEdgeSupport.annotateGuardedMutation(
                edge, method, guard.fact.unitIndex, mutation.unitIndex,
                guard.requiredOutcome, guard.reachingSuccessorIndices);
    }

    private void processFieldWrite(String method, Fact fact,
                                   Set<String> relevant, String field,
                                   List<String> sources, String kind) {
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
            addEdge(kind, source, fieldNode, method, fact);
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
            indexMutationsForField(field);
            List<FieldWrite> writers = fieldWritersByField.get(field);
            if (writers == null || writers.isEmpty()) {
                continue;
            }
            for (FieldWrite writer : writers) {
                Fact writerFact = indexedFact(writer.method,
                        writer.unitIndex);
                if (writerFact == null) {
                    continue;
                }
                Set<String> writerRelevant = relevant(writer.method);
                writerRelevant.add(writer.field);
                relevantFieldEffectsByMethod
                        .computeIfAbsent(writer.method,
                                ignored -> new LinkedHashSet<>())
                        .add(writer.field);
                selectedMethods.add(writer.method);
                processFieldWrite(writer.method, writerFact, writerRelevant,
                        writer.field, writer.sources, writer.kind);
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
        // The receiver walk only ever runs on this constructor's own call
        // sites: a demand on another constructor's receiver is that
        // constructor's own expansion, not this one's.
        if (thisRelevant || params.stream().anyMatch(
                param -> method.equals(param.constructor))) {
            forEachCallsite(constructorCallersByCallee, method,
                    (callsite, callsiteFact) ->
                            expandConstructorReceiverFields(method, thisNode,
                                    callsite, callsiteFact));
        }
        for (ConstructorParam param : params) {
            if (!expandOnce("CONSTRUCTOR_PARAM", param.constructor,
                    param.index)) {
                continue;
            }
            forEachCallsite(constructorCallersByCallee, param.constructor,
                    (callsite, callsiteFact) -> {
                if (param.index >= callsite.actuals.size()) {
                    return;
                }
                String actual = callsite.actuals.get(param.index);
                if (ignoreNode(actual)) {
                    if (addTypedLiteralCallerArgument(
                            "constructor_caller_literal_argument",
                            parseMethodSig(param.constructor), param.index,
                            callsite.method, callsiteFact)) {
                        selectedMethods.add(callsite.method);
                    }
                    return;
                }
                addEdge("constructor_caller_argument", actual, param.formal,
                        callsite.method, callsiteFact);
                relevant(callsite.method).add(actual);
                selectedMethods.add(callsite.method);
            });
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
        forEachCallsite(methodCallersByCallee, method,
                (callsite, callsiteFact) -> {
            Set<String> callerRelevant = relevant(callsite.method);
            for (int index : relevantParams) {
                if (!expandOnce("METHOD_CALLER_PARAM", method, index,
                        callsite.method, callsite.unitIndex)
                        || index >= callsite.actuals.size()) {
                    continue;
                }
                String actual = callsite.actuals.get(index);
                if (ignoreNode(actual)) {
                    if (addTypedLiteralCallerArgument(
                            "method_caller_literal_argument", callee,
                            index, callsite.method, callsiteFact)) {
                        selectedMethods.add(callsite.method);
                    }
                    continue;
                }
                addEdge("caller_argument", actual,
                        formalParam(callee, index), callsite.method,
                        callsiteFact);
                callerRelevant.add(actual);
                selectedMethods.add(callsite.method);
            }
            addReceiverFieldEffectPathGuards(method,
                    callsite, callsiteFact, callerRelevant);
            if (thisRelevant) {
                expandCallerReceiver(false, method, thisNode, callsite,
                        callsiteFact);
            }
        });
    }

    private void selectActivationCaller(String kind, String targetMethod,
                                        String callerMethod, Fact callsite,
                                        boolean emitActivationEdge) {
        if (callerMethod == null || callsite == null
                || !expandOnce(kind, targetMethod, callerMethod,
                callsite.unitIndex)) {
            return;
        }
        SootMethod caller = concreteMethod(callerMethod);
        if (caller != null) {
            loadMethod(caller);
        }
        String activation = targetMethod + ".activation";
        if (emitActivationEdge) {
            addEdge(kind, factNode(callsite), activation, callerMethod,
                    callsite);
        }
        selectedMethods.add(callerMethod);

        forEachGuardOperand(callerMethod, controllingGuards(callerMethod,
                callsite), (guard, guardNode) -> {
            addEdge("activation_path_guard", guardNode, activation,
                    callerMethod, guard.fact);
            relevant(callerMethod).add(guardNode);
        });
    }

    /**
     * Emits the constant a caller passes for an already relevant formal, and
     * answers whether the argument is one: a typed literal makes its caller
     * part of the slice even though no local carries the value.
     */
    private boolean addTypedLiteralCallerArgument(
            String kind, MethodSig callee, int argumentIndex,
            String callerMethod, Fact fact) {
        Value literal = invokeArgument(fact, argumentIndex);
        if (callee == null || !(literal instanceof Constant)
                || argumentIndex < 0
                || argumentIndex >= callee.params.size()
                || typedLiteralValue(literal,
                        callee.params.get(argumentIndex)).isEmpty()) {
            return false;
        }
        Map<String, Object> edge = addEdge(kind, factNode(fact),
                formalParam(callee, argumentIndex), callerMethod, fact);
        if (edge != null) {
            edge.put("argumentIndex", argumentIndex);
        }
        return true;
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
     * argument is a constant.
     */
    private void addReceiverFieldEffectPathGuards(
            String calleeMethod, Callsite callsite, Fact callsiteFact,
            Set<String> callerRelevant) {
        Set<String> effectFields = relevantFieldEffectsByMethod.get(
                calleeMethod);
        if (effectFields == null || effectFields.isEmpty()) {
            return;
        }
        forEachGuardOperand(callsite.method, controllingGuards(
                callsite.method, callsiteFact), (guard, guardNode) -> {
            for (String effectField : effectFields) {
                if (expandOnce("RECEIVER_EFFECT_GUARD", calleeMethod,
                        callsite.method, callsite.unitIndex,
                        guard.fact.unitIndex, guardNode, effectField)) {
                    addReceiverFieldEffectPathGuardEdge(
                            guardNode, effectField, calleeMethod,
                            callsite, guard);
                }
            }
            callerRelevant.add(guardNode);
            selectedMethods.add(callsite.method);
        });
    }

    private void addReceiverFieldEffectPathGuardEdge(
            String guardNode, String effectField, String calleeMethod,
            Callsite callsite, ExceptionGuard guard) {
        String kind = "receiver_field_effect_path_guard";
        Map<String, Object> edge = addEdge(kind, guardNode, effectField,
                callsite.method, guard.fact);
        if (edge == null) {
            return;
        }
        ControlDependenceEdgeSupport.annotateGuardedReceiverEffect(
                edge, callsite.method, guard.fact.unitIndex,
                callsite.unitIndex, guard.requiredOutcome,
                guard.reachingSuccessorIndices, calleeMethod,
                effectField);
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

    /** Builds the reverse application index once, on the first writer or
     * caller demand. */
    private void buildGlobalStaticIndex() {
        if (globalStaticIndexBuilt) {
            return;
        }
        long startedAt = System.nanoTime();
        int indexedMethods = 0;
        int indexedFacts = 0;
        globalStaticIndexBuilt = true;
        for (SootMethod method : allMethodsBySignature.values()) {
            if (!method.isConcrete()
                    || !method.getDeclaringClass().isApplicationClass()) {
                continue;
            }
            int relevantUnits = indexGlobalMethod(method);
            if (relevantUnits == 0) {
                continue;
            }
            indexedMethods++;
            indexedFacts += relevantUnits;
        }
        LOG.info("Indexed writers for {} application fields, callers for {} constructors, "
                        + "and callers for {} methods from {} relevant units "
                        + "in {} methods "
                        + "in {} ms",
                fieldWritersByField.size(), constructorCallersByCallee.size(),
                methodCallersByCallee.size(), indexedFacts,
                indexedMethods,
                (System.nanoTime() - startedAt) / 1_000_000L);
    }

    private int indexGlobalMethod(SootMethod method) {
        Body body = activeBody(method);
        if (body == null) {
            return 0;
        }
        String methodSignature = method.getSignature();
        int relevantUnits = 0;
        int index = 0;
        for (Unit unit : body.getUnits()) {
            Set<String> fieldDefs = applicationFields(
                    unit.getDefBoxes());
            Set<String> referencedFields = new LinkedHashSet<>(fieldDefs);
            referencedFields.addAll(applicationFields(unit.getUseBoxes()));
            for (String field : referencedFields) {
                methodsReferencingField.computeIfAbsent(field,
                        ignored -> new LinkedHashSet<>())
                        .add(methodSignature);
            }
            if (!fieldDefs.isEmpty()) {
                Fact fact = new Fact(methodSignature, index, unit);
                for (String field : fieldDefs) {
                    addIndexedFieldWrite(new FieldWrite(
                            methodSignature, field, index, "field_write",
                            fieldWriteSources(methodSignature, fact, field)));
                }
                relevantUnits++;
            }

            if (unit instanceof Stmt
                    && ((Stmt) unit).containsInvokeExpr()) {
                String invoked = ((Stmt) unit).getInvokeExpr()
                        .getMethodRef().getSignature();
                MethodSig sig = parseMethodSig(invoked);
                boolean indexedInvoke = false;
                if (Debug.isBooleanMarkerSignature(invoked)) {
                    explicitFaultUnitsByMethod.computeIfAbsent(
                            methodSignature,
                            ignored -> new ArrayList<>()).add(index);
                    indexedInvoke = true;
                }
                if (sig != null && isApplicationClassName(sig.owner)) {
                    String unitText = unit.toString();
                    String receiver = canonical(methodSignature,
                            invokeBaseLocal(unitText));
                    List<String> actuals = canonicalPositionList(
                            methodSignature, actualInvokeArgs(unitText));
                    if ("<init>".equals(sig.name)) {
                        addIndexedCallsite(constructorCallersByCallee,
                                sig.raw, new Callsite(
                                        methodSignature, index, receiver,
                                        actuals));
                    } else if (!"<clinit>".equals(sig.name)) {
                        addIndexedCallsite(methodCallersByCallee, sig.raw,
                                new Callsite(methodSignature, index,
                                        receiver, actuals));
                    }
                    indexedInvoke = true;
                }
                if (indexedInvoke && fieldDefs.isEmpty()) {
                    relevantUnits++;
                }
            }
            index++;
        }
        return relevantUnits;
    }

    private Set<String> applicationFields(
            List<soot.ValueBox> boxes) {
        Set<String> fields = new LinkedHashSet<>();
        for (soot.ValueBox box : boxes) {
            if (!(box.getValue() instanceof soot.jimple.FieldRef)) {
                continue;
            }
            String field = CausynthStaticFacts.declaredFieldSignature(
                    ((soot.jimple.FieldRef) box.getValue()).getFieldRef());
            if (isApplicationField(field)) {
                fields.add(field);
            }
        }
        return fields;
    }

    private List<Fact> factsFromBody(String method, Body body) {
        List<Fact> facts = new ArrayList<>();
        int index = 0;
        for (Unit unit : body.getUnits()) {
            facts.add(new Fact(method, index++, unit));
        }
        return facts;
    }

    /** Materializes a full fact only after its reverse-index row is used. */
    private Fact indexedFact(String method, int unitIndex) {
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null) {
            SootMethod sootMethod = concreteMethod(method);
            if (sootMethod != null) {
                loadMethod(sootMethod);
            }
            facts = factsByMethod.get(method);
        }
        if (facts == null || unitIndex < 0 || unitIndex >= facts.size()) {
            return null;
        }
        Fact fact = facts.get(unitIndex);
        return fact.unitIndex == unitIndex ? fact : null;
    }

    private void addIndexedFieldWrite(FieldWrite write) {
        if (!isApplicationField(write.field)) {
            return;
        }
        fieldWritersByField.computeIfAbsent(write.field,
                ignored -> new ArrayList<>()).add(write);
    }

    /** Indexes one recorded call site under its application callee. */
    private void addIndexedCallsite(Map<String, List<Callsite>> index,
                                    String callee, Callsite callsite) {
        MethodSig sig = parseMethodSig(callee);
        if (sig == null || !isApplicationClassName(sig.owner)) {
            return;
        }
        index.computeIfAbsent(callee, ignored -> new ArrayList<>())
                .add(callsite);
    }

    /**
     * Resolves backed collection mutations only for a field already demanded
     * by the failure slice.  The previous global index ran the backwards
     * alias walk for every collection mutator in every application method;
     * almost all of those results were never queried.
     *
     * <p>This is equivalent to the eager scan: {@link #fieldsAliasedByLocal}
     * can return a field only when that same method contains a direct Jimple
     * reference to it, which is exactly the candidate map built above.</p>
     */
    private void indexMutationsForField(String field) {
        if (!mutationIndexedFields.add(field)) {
            return;
        }
        for (String method : methodsReferencingField.getOrDefault(field,
                Collections.emptySet())) {
            List<Fact> facts = factsByMethod.get(method);
            if (facts == null) {
                Body body = activeBody(concreteMethod(method));
                if (body == null) {
                    continue;
                }
                facts = factsFromBody(method, body);
            }
            for (Fact fact : facts) {
                if (!fieldsMutatedByInvoke(facts, fact.unitIndex)
                        .contains(field)) {
                    continue;
                }
                addIndexedFieldWrite(new FieldWrite(
                        method, field, fact.unitIndex, "field_mutation",
                        fieldMutationSources(method, fact, field)));
            }
        }
    }

    private List<String> fieldWriteSources(String method, Fact fact, String field) {
        List<String> raw = new ArrayList<>();
        raw.addAll(localValueUses(fact));
        raw.addAll(actualInvokeArgs(fact.unitText));
        raw.addAll(fact.fieldUses);
        // In Jimple, the base of an instance-field assignment is a use box,
        // but it selects the destination object; it is not the value written
        // into the field.
        Set<String> destinationBases = new LinkedHashSet<>();
        for (InstanceFieldAccess access : fact.instanceFieldDefs) {
            if (field.equals(access.field)) {
                destinationBases.add(access.base);
            }
        }
        raw.removeIf(destinationBases::contains);
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
            if (!exactIntersects(work, defs)) {
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
     * Models only Java collection APIs whose returned object is specified to
     * remain backed by the receiver.
     */
    private boolean returnsBackedCollectionView(Fact fact) {
        MethodSig invoked = parseMethodSig(fact.invoke);
        if (invoked == null || fact.defs.isEmpty()
                || invokeBaseLocal(fact.unitText) == null) {
            return false;
        }
        String owner = invoked.owner;
        if (!owner.startsWith("java.util.")) {
            return false;
        }
        return owner.contains("Map") || "java.util.Hashtable".equals(owner)
                ? BACKED_MAP_VIEWS.contains(invoked.name)
                : BACKED_ITERATORS.contains(invoked.name);
    }

    private boolean isFieldMutator(Fact fact) {
        MethodSig sig = parseMethodSig(fact.invoke);
        if (sig == null) {
            return false;
        }
        return CONTAINER_MUTATORS.contains(sig.name)
                || ("java.util.concurrent.atomic.AtomicInteger".equals(
                        sig.owner)
                || "java.util.concurrent.atomic.AtomicLong".equals(sig.owner))
                && ATOMIC_NUMERIC_MUTATIONS.contains(sig.name);
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
        if (Debug.isBooleanMarkerSignature(callee.raw)) {
            propagateCallReturns("explicit_symbolic_fault",
                    callerMethod, fact, callee.raw, defs,
                    callerRelevant, Collections.<String>emptySet(),
                    false);
            annotateExplicitSymbolicFault(callerMethod, fact, callee, defs,
                    callerRelevant);
            return;
        }
        processSemanticContainerOperation(callerMethod, fact,
                callee, defs, callerRelevant);
        processSemanticContainerMutation(callerMethod, fact,
                callee, callerRelevant);
        processAccessorInvoke(callerMethod, fact, callee, defs,
                callerRelevant);
        List<String> actuals = canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText));
        processContainerCallMutationEffects(callerMethod, fact, callee,
                actuals, callerRelevant);
        processConstructorObjectInvoke(callerMethod, fact, callee,
                actuals, callerRelevant);
        boolean dynamicDispatch = !resolveDispatchTargets(callee)
                .isEmpty();
        boolean modeledContainerResult =
                JavaContainerTypes.symbolicResultOperation(callee.raw);
        boolean expandableCallee = isExpandableMethod(callee.raw);
        SootMethod calleeMethod = expandableCallee
                ? concreteMethod(callee.raw) : null;
        if (expandableCallee) {
            loadMethod(calleeMethod);
        }
        Set<String> calleeRelevant = expandableCallee
                ? relevant(callee.raw)
                : Collections.emptySet();

        if (!dynamicDispatch) {
            propagateCallArguments("call_argument",
                    callerMethod, fact, callee, actuals,
                    callerRelevant, calleeRelevant, expandableCallee);
            if (!modeledContainerResult) {
                propagateCallReturns("call_return",
                        callerMethod, fact, callee.raw, defs,
                        callerRelevant, calleeRelevant,
                        expandableCallee);
            }
        }
        processDispatchInvoke(callerMethod, fact, callee, defs, actuals,
                callerRelevant);
    }

    private void annotateExplicitSymbolicFault(
            String callerMethod, Fact fact, MethodSig callee,
            List<String> defs, Set<String> callerRelevant) {
        String name = explicitFaultName(fact);
        for (String def : defs) {
            if (!callerRelevant.contains(def)) continue;
            Map<String, Object> edge = emittedEdgeRows.get(edgeKey(
                    "explicit_symbolic_fault", callee.raw + ".return", def,
                    callerMethod, fact));
            annotateExplicitSymbolicFaultEdge(edge, callerMethod, fact,
                    name);
        }
    }

    private static void annotateExplicitSymbolicFaultEdge(
            Map<String, Object> edge, String callerMethod, Fact fact,
            String name) {
        if (edge == null) return;
        edge.put("explicitSymbolicFault", true);
        edge.put("symbolicName", name.isEmpty()
                ? SiteId.of(callerMethod, fact.unitIndex) : name);
    }

    private static String explicitFaultName(Fact fact) {
        if (!(fact.unit instanceof Stmt)) return "";
        InvokeExpr invoke = ((Stmt) fact.unit).getInvokeExpr();
        if (invoke.getArgCount() != 1
                || !(invoke.getArg(0) instanceof StringConstant)) {
            return "";
        }
        return ((StringConstant) invoke.getArg(0)).value;
    }

    /**
     * One forward argument walk for an ordinary Java call.
     */
    private boolean propagateCallArguments(
            String kind, String callerMethod, Fact fact,
            MethodSig target, List<String> actuals,
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
            if (!targetExpandable || !targetRelevant.contains(formal)) {
                continue;
            }
            relevantFlow = true;
            if (kind != null) {
                addEdge(kind, actual, formal, callerMethod, fact);
            }
            callerRelevant.add(actual);
        }
        return relevantFlow;
    }

    /** The same walk over a call's returned value; see the arguments above. */
    private void propagateCallReturns(
            String kind, String callerMethod, Fact fact,
            String targetMethod, List<String> defs,
            Set<String> callerRelevant, Set<String> targetRelevant,
            boolean targetExpandable) {
        String returnNode = targetMethod + ".return";
        for (String def : defs) {
            if (!callerRelevant.contains(def)) {
                continue;
            }
            if (kind != null) {
                addEdge(kind, returnNode, def, callerMethod, fact);
            }
            if (targetExpandable) {
                targetRelevant.add(returnNode);
                selectedMethods.add(targetMethod);
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
                || isSemanticContainerView(callee))) {
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
        // Reaching this point proves that the operation's result is already
        // in the failure-directed backward slice.  Its receiver state is
        // therefore semantic input even when the selected member is later
        // used as an object receiver: the concrete receiver still identifies
        // the Map object, while the VM models that object's bounded contents.
        String dependencyRole = DependencyRole.VALUE_FRONTIER;
        for (String def : relevantDefs) {
            Map<String, Object> edge = addEdge("container_receiver",
                    receiverNode, def, callerMethod, fact);
            if (edge != null) {
                edge.put("dependencyRole", dependencyRole);
            }
        }
        callerRelevant.add(receiverNode);

        for (String argument : canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText))) {
            if (ignoreNode(argument)) continue;
            for (String def : relevantDefs) {
                addEdge("container_argument", argument, def,
                        callerMethod, fact);
            }
            callerRelevant.add(argument);
        }
    }

    /**
     * A modeled container's state after a mutator depends on the values
     * inserted into it.  This is the mutation counterpart of
     * {@link #processSemanticContainerOperation}: once a later result makes
     * the receiver relevant, pull the exact mutator arguments into the
     * backward slice.  The VM container algebra owns the value semantics;
     * this edge only records the ordinary data dependency.
     */
    private void processSemanticContainerMutation(
            String callerMethod, Fact fact, MethodSig callee,
            Set<String> callerRelevant) {
        if (callee == null
                || !JavaContainerTypes.modeledContainerMutator(callee.raw)) {
            return;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) return;
        String receiverNode = canonical(callerMethod, receiver);
        if (ignoreNode(receiverNode)
                || !callerRelevant.contains(receiverNode)) {
            return;
        }
        for (String argument : canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText))) {
            if (ignoreNode(argument)) continue;
            addEdge("container_mutation_argument", argument, receiverNode,
                    callerMethod, fact);
            callerRelevant.add(argument);
        }
    }

    /** Bridges an application helper that mutates a container argument. */
    private void processContainerCallMutationEffects(
            String callerMethod, Fact fact, MethodSig callee,
            List<String> actuals, Set<String> callerRelevant) {
        for (Map.Entry<Integer, String> mutation :
                directlyMutatedContainerParameters(callee).entrySet()) {
            int index = mutation.getKey();
            if (index < 0 || index >= actuals.size()) continue;
            String actual = actuals.get(index);
            if (ignoreNode(actual) || !callerRelevant.contains(actual)) {
                continue;
            }
            String parameterLocal = mutation.getValue();
            addEdge("container_call_mutation_effect", parameterLocal, actual,
                    callerMethod, fact);
            relevant(callee.raw).add(parameterLocal);
            selectedMethods.add(callee.raw);
        }
    }

    private Map<Integer, String> directlyMutatedContainerParameters(
            MethodSig callee) {
        if (callee == null) return Collections.emptyMap();
        return memoized(directlyMutatedContainerParametersCache,
                callee.raw, ignored -> {
            SootMethod method = allMethodsBySignature.get(callee.raw);
            if (method == null || !method.isConcrete()
                    || !method.getDeclaringClass().isApplicationClass()) {
                return Collections.<Integer, String>emptyMap();
            }
            loadMethod(method);
            List<Fact> facts = factsByMethod.get(callee.raw);
            if (facts == null) {
                return Collections.<Integer, String>emptyMap();
            }

            Map<String, Integer> parameterLocals = new LinkedHashMap<>();
            for (Fact fact : facts) {
                Matcher parameter = PARAMETER_REFERENCE_PATTERN.matcher(
                        fact.unitText);
                if (!parameter.find()) continue;
                int index = Integer.parseInt(parameter.group(1));
                for (String def : canonicalDefs(callee.raw, fact)) {
                    if (!ignoreNode(def)) parameterLocals.put(def, index);
                }
            }

            Map<Integer, String> result = new LinkedHashMap<>();
            for (Fact fact : facts) {
                if (!JavaContainerTypes.modeledContainerMutator(fact.invoke)) {
                    continue;
                }
                String receiver = invokeBaseLocal(fact.unitText);
                Integer index = receiver == null ? null : parameterLocals.get(
                        canonical(callee.raw, receiver));
                if (index != null) {
                    result.put(index, canonical(callee.raw, receiver));
                }
            }
            return result.isEmpty()
                    ? Collections.<Integer, String>emptyMap()
                    : Collections.unmodifiableMap(result);
        });
    }

    private boolean isSemanticContainerView(MethodSig method) {
        if (method == null) return false;
        if (MAP_CONTRACT_OWNERS.contains(method.owner)
                && method.params.isEmpty()) {
            if ("values".equals(method.name)
                    && "java.util.Collection".equals(method.returnType)
                    || ("keySet".equals(method.name)
                    || "entrySet".equals(method.name))
                    && "java.util.Set".equals(method.returnType)) {
                return true;
            }
        }
        return COLLECTION_CONTRACT_OWNERS.contains(method.owner)
                && "toArray".equals(method.name)
                && method.returnType.endsWith("[]")
                && (method.params.isEmpty()
                || (method.params.size() == 1
                && method.params.get(0).endsWith("[]")));
    }

    /** A Map.get result depends on both the lookup key and the map state. */
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
                    callerMethod, fact);
            callerRelevant.add(actual);
        }
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
            annotateAccessorDeclaredFieldEdge(
                    addEdge("accessor_field_return", declaredFieldNode,
                            def, callerMethod, fact),
                    declaredField, accessor.implementation);
            addEdge("accessor_receiver", receiverNode, def,
                    callerMethod, fact);
        }
        callerRelevant.add(receiverNode);
        callerRelevant.add(declaredFieldNode);
    }

    private void annotateAccessorDeclaredFieldEdge(
            Map<String, Object> edge, SootField field, SootMethod accessor) {
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
     * Attaches the resolved Java declaration to one exact direct field read.
     */
    private void annotateDirectDeclaredFieldEdge(Map<String, Object> edge,
                                                 String fieldSignature) {
        String owner = fieldOwner(fieldSignature);
        Matcher name = FIELD_NAME_PATTERN.matcher(
                fieldSignature == null ? "" : fieldSignature);
        SootField field = resolveDeclaredField(owner,
                name.matches() ? name.group(1) : "");
        if (edge == null || field == null
                || !field.getSignature().equals(fieldSignature)) {
            return;
        }
        edge.put("declaredFieldSignature", field.getSignature());
    }

    /** Resolves one method declaration inherited by the invocation owner. */
    private SootMethod resolveDeclaredMethod(MethodSig methodSignature) {
        if (methodSignature == null || methodSignature.owner.isEmpty()) {
            return null;
        }
        String subSignature = methodSubSignature(methodSignature);
        return resolveInHierarchy(methodSignature.owner, sootClass -> {
            for (SootMethod method : sootClass.getMethods()) {
                if (subSignature.equals(method.getSubSignature())) {
                    return method;
                }
            }
            return null;
        });
    }

    /**
     * Returns the unique analyzable implementation that can receive this
     * invocation in the closed Soot world.
     */
    private SootMethod uniqueAnalyzableImplementation(MethodSig callee) {
        if (callee == null || callee.owner.isEmpty()) {
            return null;
        }
        if (classesByName.get(callee.owner) == null
                && Scene.v().getSootClassUnsafe(callee.owner) == null) {
            return null;
        }
        Set<SootMethod> candidates = new LinkedHashSet<>();
        SootMethod declared = resolveDeclaredMethod(callee);
        if (eligibleAnalyzableImplementation(declared)) {
            candidates.add(declared);
        }
        candidates.addAll(concreteImplementations(callee,
                this::eligibleAnalyzableImplementation));
        return candidates.size() == 1
                ? candidates.iterator().next() : null;
    }

    private boolean eligibleAnalyzableImplementation(SootMethod method) {
        return method != null && method.isConcrete() && !method.isStatic()
                && !method.isNative() && activeBody(method) != null;
    }

    /**
     * Recognizes a field accessor from its complete Jimple body, never from
     * class or method spelling.
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
                callee, uniqueAnalyzableImplementation(callee));
        structuralFieldAccessors.put(callee.raw, resolved);
        return resolved;
    }

    private StructuralFieldAccessor inspectStructuralFieldAccessor(
            MethodSig callee, SootMethod method) {
        if (callee == null || !callee.params.isEmpty()
                || "void".equals(erasedTypeName(callee.returnType))) {
            return null;
        }
        SootField field = StructuralFieldAccessorProof.exactField(method);
        if (field == null
                || !erasedTypeName(field.getType().toString()).equals(
                erasedTypeName(callee.returnType))
                || !erasedTypeName(method.getReturnType().toString()).equals(
                erasedTypeName(callee.returnType))) {
            return null;
        }
        return new StructuralFieldAccessor(method, field);
    }

    private void processDispatchInvoke(String callerMethod, Fact fact,
                                       MethodSig callee, List<String> defs,
                                       List<String> actuals,
                                       Set<String> callerRelevant) {
        List<String> targetMethods = resolveDispatchTargets(callee);
        if (targetMethods.isEmpty()) {
            return;
        }
        targetMethods = CausynthPipeline.conservativeDispatchTargets(
                targetMethods);
        for (String targetMethod : targetMethods) {
            if (targetMethod.equals(callee.raw)) {
                continue;
            }
            SootMethod sootMethod = concreteMethod(targetMethod);
            if (sootMethod == null) {
                continue;
            }
            loadMethod(sootMethod);
            MethodSig targetSig = parseMethodSig(targetMethod);
            if (targetSig == null) {
                continue;
            }
            Set<String> targetRelevant = relevant(targetMethod);
            boolean callRelevant = exactIntersects(callerRelevant, defs);
            callRelevant |= propagateCallArguments("dispatch_argument",
                    callerMethod, fact, targetSig, actuals,
                    callerRelevant, targetRelevant, true);
            propagateCallReturns("dispatch_return",
                    callerMethod, fact, targetMethod, defs,
                    callerRelevant, targetRelevant, true);
            String callerReceiver = canonical(callerMethod,
                    invokeBaseLocal(fact.unitText));
            String targetThis = methodThisNode(targetMethod);
            if (callRelevant && targetThis != null
                    && !ignoreNode(callerReceiver)) {
                addEdge("dispatch_receiver", callerReceiver, targetThis,
                        callerMethod, fact);
                callerRelevant.add(callerReceiver);
                targetRelevant.add(targetThis);
                selectedMethods.add(targetMethod);
            }
        }
    }

    private List<String> resolveDispatchTargets(MethodSig callee) {
        if (callee == null || skipDispatchOwner(callee.owner)) {
            return Collections.emptyList();
        }
        return memoized(dispatchTargetsCache, callee.raw, ignored -> {
            SootClass owner = classesByName.get(callee.owner);
            if (owner == null
                    || (!owner.isInterface() && !owner.isAbstract())) {
                return Collections.<String>emptyList();
            }
            List<String> targets = applicationImplementationSignatures(
                    callee);
            return targets.isEmpty() ? Collections.<String>emptyList()
                    : Collections.unmodifiableList(targets);
        });
    }

    private String methodSubSignature(MethodSig sig) {
        return sig.returnType + " " + sig.name + "("
                + String.join(",", sig.params) + ")";
    }

    /** Indexed concrete methods below {@code sig.owner} that {@code accept}s. */
    private List<SootMethod> concreteImplementations(
            MethodSig sig, Predicate<SootMethod> accept) {
        List<SootMethod> candidates = concreteMethodsBySubSignature.get(
                methodSubSignature(sig));
        if (candidates == null) {
            return Collections.emptyList();
        }
        List<SootMethod> matches = new ArrayList<>();
        for (SootMethod candidate : candidates) {
            if (accept.test(candidate) && classImplementsOrExtends(
                    candidate.getDeclaringClass(), sig.owner)) {
                matches.add(candidate);
            }
        }
        return matches;
    }

    private List<String> applicationImplementationSignatures(MethodSig sig) {
        List<String> signatures = new ArrayList<>();
        for (SootMethod implementation : concreteImplementations(sig,
                method -> method.getDeclaringClass().isApplicationClass())) {
            signatures.add(implementation.getSignature());
        }
        return signatures;
    }

    private boolean skipDispatchOwner(String owner) {
        return owner == null
                || owner.startsWith("java.")
                || owner.startsWith("javax.")
                || owner.startsWith("com.google.")
                || owner.startsWith("org.slf4j.");
    }

    private Fact captureFact(WireFlowCatalog.CaptureSite site) {
        if (site.unitIndex >= 0) {
            return indexedFact(site.method, site.unitIndex);
        }
        List<Fact> facts = factsByMethod.get(site.method);
        if (facts == null) return null;
        for (Fact fact : facts) {
            if (WireFlowCatalog.CaptureSite.METHOD_RETURN.equals(site.kind)
                    && fact.isReturn) return fact;
            if (WireFlowCatalog.CaptureSite.METHOD_PARAMETER.equals(site.kind)
                    && fact.unitText.contains("@parameter" + site.index)) {
                return fact;
            }
        }
        return null;
    }

    private String captureNode(WireFlowCatalog.CaptureSite site, Fact fact) {
        MethodSig signature = parseMethodSig(site.method);
        if (WireFlowCatalog.CaptureSite.METHOD_PARAMETER.equals(site.kind)) {
            return signature == null ? "" : formalParam(signature, site.index);
        }
        if (WireFlowCatalog.CaptureSite.METHOD_RETURN.equals(site.kind)) {
            return site.method + ".return";
        }
        if (fact == null) return "";
        if (WireFlowCatalog.CaptureSite.CALL_ARGUMENT.equals(site.kind)) {
            List<String> actuals = canonicalPositionList(site.method,
                    actualInvokeArgs(fact.unitText));
            if (site.index >= actuals.size()) return "";
            String actual = actuals.get(site.index);
            return ignoreNode(actual) ? factNode(fact) : actual;
        }
        List<String> defs = canonicalDefs(site.method, fact);
        return defs.isEmpty() ? factNode(fact) : defs.get(0);
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
            forEachCallsite(methodCallersByCallee, sourceMethod,
                    (callsite, callsiteFact) -> {
                Set<String> callerRelevant = relevant(callsite.method);
                boolean relevantFlow = expandCallerArguments(
                        "DISPATCH_CALLER_PARAM",
                        "dispatch_caller_argument",
                        targetMethod, sourceMethod, targetSig, targetRelevant,
                        callsite, callsiteFact, callerRelevant);
                if (targetThisRelevant) {
                    relevantFlow |= expandCallerReceiver(true, targetMethod,
                            targetThis, callsite, callsiteFact);
                }
                if (relevantFlow) {
                    selectActivationCaller("dispatch_activation",
                            targetMethod, callsite.method, callsiteFact, true);
                }
            });
        }
    }

    /**
     * The one walk every call-site expander takes: visit each recorded call
     * site of {@code callee} the static index can name a fact for, in index
     * order. Constructor, method, RPC and dispatch callers differ only in
     * what they demand at a site, never in how the sites are found.
     * ({@code expandFieldWriters} walks field-write rows, not call sites.)
     */
    private void forEachCallsite(
            Map<String, List<Callsite>> index, String callee,
            BiConsumer<Callsite, Fact> visit) {
        List<Callsite> callsites = index.get(callee);
        if (callsites == null) {
            return;
        }
        for (Callsite callsite : callsites) {
            Fact callsiteFact = indexedFact(callsite.method,
                    callsite.unitIndex);
            if (callsiteFact != null) {
                visit.accept(callsite, callsiteFact);
            }
        }
    }

    /**
     * One backward argument expansion at one call site: for every (actual,
     * formal) positional pair the site binds, demand the caller's actual when
     * the callee's formal is already relevant.
     */
    private boolean expandCallerArguments(
            String demandKind, String edgeKind,
            String targetMethod, String demandScope, MethodSig target,
            Set<String> targetRelevant, Callsite callsite,
            Fact callsiteFact, Set<String> callerRelevant) {
        boolean expanded = false;
        int count = Math.min(callsite.actuals.size(), target.params.size());
        for (int index = 0; index < count; index++) {
            String formal = formalParam(target, index);
            Object[] demand = new Object[]{targetMethod, demandScope, index,
                    callsite.method, callsite.unitIndex};
            if (!targetRelevant.contains(formal)
                    || !expandOnce(demandKind, demand)) {
                continue;
            }
            String actual = callsite.actuals.get(index);
            if (ignoreNode(actual)) {
                continue;
            }
            if (edgeKind != null) {
                addEdge(edgeKind, actual, formal, callsite.method,
                        callsiteFact);
            }
            callerRelevant.add(actual);
            selectedMethods.add(callsite.method);
            expanded = true;
        }
        return expanded;
    }

    private boolean expandCallerReceiver(
            boolean dispatch, String targetMethod, String targetThis,
            Callsite callsite, Fact callsiteFact) {
        if (targetThis == null || callsite == null
                || ignoreNode(callsite.receiver)) {
            return false;
        }
        String demand = dispatch ? "DISPATCH_CALLER_RECEIVER"
                : "METHOD_CALLER_RECEIVER";
        String kind = dispatch ? "dispatch_caller_receiver"
                : "method_receiver";
        if (relevant(targetMethod).contains(targetThis)
                && expandOnce(demand, targetMethod,
                callsite.method, callsite.unitIndex)) {
            addEdge(kind, callsite.receiver,
                    targetThis, callsite.method, callsiteFact);
            relevant(callsite.method).add(callsite.receiver);
            selectedMethods.add(callsite.method);
            return true;
        }
        return false;
    }

    private List<String> resolveDispatchSources(String targetMethod) {
        return memoized(dispatchSourcesCache, targetMethod, ignored -> {
            MethodSig targetSig = parseMethodSig(targetMethod);
            if (targetSig == null || skipDispatchOwner(targetSig.owner)) {
                return Collections.<String>emptyList();
            }
            SootClass targetClass = classesByName.get(targetSig.owner);
            if (targetClass == null) {
                return Collections.<String>emptyList();
            }
            Set<String> sources = new LinkedHashSet<>();
            String subSignature = methodSubSignature(targetSig);
            for (String candidateName : hierarchyNames(targetClass)) {
                SootClass candidate = classesByName.get(candidateName);
                if (candidate == null || !candidate.isApplicationClass()
                        || skipDispatchOwner(candidate.getName())
                        || (!candidate.isInterface()
                        && !candidate.isAbstract())) {
                    continue;
                }
                for (SootMethod method : candidate.getMethods()) {
                    if (subSignature.equals(method.getSubSignature())) {
                        sources.add(method.getSignature());
                    }
                }
            }
            return sources.isEmpty() ? Collections.<String>emptyList()
                    : Collections.unmodifiableList(
                            new ArrayList<>(sources));
        });
    }

    private boolean isExpandableMethod(String signature) {
        SootMethod method = concreteMethod(signature);
        MethodSig sig = parseMethodSig(signature);
        return method != null
                && method.isConcrete()
                && method.getDeclaringClass().isApplicationClass()
                && !method.getDeclaringClass().isInterface()
                && !method.getDeclaringClass().isAbstract()
                && structuralFieldAccessor(sig) == null;
    }

    private Set<String> relevant(String method) {
        return relevantByMethod.computeIfAbsent(method, DirtyMarkingSet::new);
    }

    /** One computation per key, taken on first demand and kept. */
    private static <K, V> V memoized(Map<K, V> cache, K key,
                                     Function<K, V> compute) {
        V cached = cache.get(key);
        if (cached != null) {
            return cached;
        }
        V computed = compute.apply(key);
        cache.put(key, computed);
        return computed;
    }

    /**
     * Visits every causal operand of {@code guards}, as the canonical node it
     * names in {@code method}, skipping the ones no edge may name.
     */
    private void forEachGuardOperand(
            String method, List<ExceptionGuard> guards,
            BiConsumer<ExceptionGuard, String> visit) {
        for (ExceptionGuard guard : guards) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(method, use);
                if (!ignoreNode(guardNode)) {
                    visit.accept(guard, guardNode);
                }
            }
        }
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

    private final class DirtyMarkingSet extends LinkedHashSet<String> {
        /** The method to mark, or null to mark the added value itself. */
        private final String method;

        private DirtyMarkingSet(String method) {
            this.method = method;
        }

        @Override
        public boolean add(String value) {
            if (!super.add(value)) return false;
            markDirty(method == null ? value : method);
            return true;
        }

    }

    private List<String> nonInvokeUses(Fact fact) {
        return memoized(nonInvokeUsesCache, fact, ignored -> {
            List<String> uses = new ArrayList<>();
            for (String use : fact.uses) {
                if (!use.startsWith("virtualinvoke ")
                        && !use.startsWith("interfaceinvoke ")
                        && !use.startsWith("specialinvoke ")
                        && !use.startsWith("staticinvoke ")) {
                    uses.add(use);
                }
            }
            return uses.isEmpty() ? Collections.<String>emptyList()
                    : Collections.unmodifiableList(uses);
        });
    }

    private List<String> localValueUses(Fact fact) {
        return memoized(localValueUsesCache, fact, ignored -> {
            String invokeBase = invokeBaseLocal(fact.unitText);
            Set<String> applicationInvokeArgs = new LinkedHashSet<>();
            MethodSig invoked = parseMethodSig(fact.invoke);
            boolean applicationInvoke = invoked != null
                    && isApplicationClassName(invoked.owner);
            boolean valueLikeLibraryInvoke = isValueLikeLibraryInvoke(invoked);
            if (applicationInvoke) {
                applicationInvokeArgs.addAll(actualInvokeArgs(fact.unitText));
            }
            Set<String> arrayStructureOperands = new LinkedHashSet<>();
            if (fact.arrayDef != null) {
                arrayStructureOperands.add(fact.arrayDef.base);
                arrayStructureOperands.add(fact.arrayDef.index);
            }
            if (fact.arrayUse != null) {
                arrayStructureOperands.add(fact.arrayUse.base);
                arrayStructureOperands.add(fact.arrayUse.index);
            }
            Set<String> uses = new LinkedHashSet<>();
            for (String use : nonInvokeUses(fact)) {
                // Soot exposes both a composite expression and each of its leaf
                // operands through Unit.getUseBoxes().
                if (!atomicDataflowUse(use)
                        || (!valueLikeLibraryInvoke && use.equals(invokeBase))
                        || applicationInvokeArgs.contains(use)
                        || arrayStructureOperands.contains(use)
                        || isFieldAccessValue(use)) {
                    continue;
                }
                // Unit.getUseBoxes() can report both a cast expression and its
                // leaf local.
                String leafLocal = localName(use);
                uses.add(leafLocal == null ? use : leafLocal);
            }
            return uses.isEmpty() ? Collections.<String>emptyList()
                    : Collections.unmodifiableList(
                            new ArrayList<>(uses));
        });
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
        if (invoked.params.isEmpty() && VALUE_LIKE_UNBOXING.contains(
                owner + "." + invoked.name)) {
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
        return memoized(cache, fact, ignored -> {
            List<String> canonical = canonicalList(method, values);
            return canonical.isEmpty() ? Collections.<String>emptyList()
                    : Collections.unmodifiableList(canonical);
        });
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
        return SiteId.of(fact.method, fact.unitIndex);
    }

    /** Returns the canonical local bound to {@code @this}. */
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

    private void expandConstructorReceiverFields(String constructor,
                                                 String constructorThis,
                                                 Callsite callsite,
                                                 Fact callsiteFact) {
        if (constructorThis == null || ignoreNode(callsite.receiver)) {
            return;
        }
        if (relevant(constructor).contains(constructorThis)
                && expandOnce("CONSTRUCTOR_CALLER_RECEIVER", constructor,
                callsite.method, callsite.unitIndex)) {
            addEdge("constructor_receiver", callsite.receiver,
                    constructorThis,
                    callsite.method, callsiteFact);
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
        return resolveInHierarchy(owner, sootClass ->
                CausynthStaticFacts.field(sootClass,
                        field -> fieldName.equals(field.getName())));
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
        return walkHierarchy(root, resolver);
    }

    /** The one hierarchy walk: first non-null answer, or null. */
    private static <T> T walkHierarchy(SootClass root,
                                       Function<SootClass, T> resolver) {
        if (root == null) {
            return null;
        }
        Set<SootClass> seen = new LinkedHashSet<>();
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

    private Map<String, Object> addEdge(String kind, Object from, Object to,
                                        String method, Fact fact) {
        if (from == null || to == null) {
            return null;
        }
        String fromText = String.valueOf(from);
        String toText = String.valueOf(to);
        boolean sameCellPathGuard =
                ControlDependenceEdgeSupport.permitsSameCellEdge(kind,
                        fromText, toText, fact != null);
        if (ignoreNode(fromText) || ignoreNode(toText)
                || fromText.equals(toText) && !sameCellPathGuard) {
            return null;
        }
        EdgeIdentity key = edgeKey(kind, fromText, toText, method, fact);
        Map<String, Object> edge = emittedEdgeRows.get(key);
        if (edge == null) {
            String edgeId = "DF." + edgeCounter++;
            String edgeTransferKind = StaticDataflowEdgeSchema.transferKind(
                    kind,
                    fact == null ? "" : fact.unitText,
                    fact == null ? null : fact.invoke,
                    fromText, toText);
            boolean exactDirectCopy = exactLocalDirectCopy(kind,
                    fromText, toText,
                    method, fact, edgeTransferKind);
            edge = object(
                    "schemaVersion", StaticDataflowEdgeSchema.VERSION,
                    "id", edgeId,
                    "kind", kind,
                    "transferKind", edgeTransferKind,
                    "fromCell", fromText,
                    "toCell", toText,
                    "method", method,
                    "siteId", stableSiteId(method,
                            fact == null ? -1 : fact.unitIndex, kind));
            if (exactDirectCopy) {
                edge.put("valueFlowAuthority",
                        fact.unit instanceof IdentityStmt
                                ? "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1"
                                : "SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
            }
            if (fact != null) {
                edge.put("unitIndex", fact.unitIndex);
                if (canonicalDefs(method, fact).contains(toText)) {
                    edge.put("definitionSite", true);
                }
                if (fact.unit instanceof DefinitionStmt
                        && ((DefinitionStmt) fact.unit).getRightOp()
                        instanceof soot.jimple.LengthExpr) {
                    edge.put("arrayLengthOperation", true);
                }
                if (fact.isBranch && loopControlGuard(method, fact.unit)) {
                    edge.put("loopControlGuard", true);
                }
                if (fact.invoke != null) {
                    edge.put("invoke", fact.invoke);
                }
            }
            emittedEdgeRows.put(key, edge);
        }
        return edge;
    }

    private boolean loopControlGuard(String method, Unit unit) {
        MethodControlFlow controlFlow = controlFlow(method);
        return controlFlow != null
                && controlFlow.loopControlGuards().contains(unit);
    }

    /**
     * Proves that one ordinary {@code local_def_use} row is an exact JVM value
     * copy.
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
        // A concrete Soot unit is part of a causal edge's identity.
        return new EdgeIdentity(String.valueOf(kind), String.valueOf(from),
                String.valueOf(to), String.valueOf(method),
                fact != null, fact == null ? -1 : fact.unitIndex);
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

    /** Exact replacement for the old newline-joined edge key. */
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

    private static final class MethodControlFlow {
        /** The method's one loop CFG: its ordinary transfers, and the
         *  dominance its guards are proved on. */
        private final CfgLoopControl.LoopCfg cfg;
        private Set<Unit> loopControlGuards;

        private MethodControlFlow(CfgLoopControl.LoopCfg cfg) {
            this.cfg = cfg;
        }

        private Set<Unit> loopControlGuards() {
            if (loopControlGuards == null) {
                loopControlGuards = CfgLoopControl.guards(cfg);
            }
            return loopControlGuards;
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
        Matcher matcher =
                CausynthStaticFacts.METHOD_SIGNATURE.matcher(raw);
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

    private static Set<String> names(String... values) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(values)));
    }

    private static Map<String, Object> object(Object... keyValues) {
        Map<String, Object> map = new LinkedHashMap<>();
        for (int i = 0; i + 1 < keyValues.length; i += 2) {
            map.put(String.valueOf(keyValues[i]), keyValues[i + 1]);
        }
        return map;
    }
}
