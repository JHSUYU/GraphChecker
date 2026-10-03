package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.annotation.Debug;

import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.plan.DependencyRole;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
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
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceInvokeExpr;
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

import static edu.uva.liftlab.graphchecker.causynth.MapFields.object;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.Callsite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ConstructorParam;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ArrayAccess;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.Fact;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.FieldWrite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.InstanceFieldAccess;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.actualInvokeArgs;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.activeBody;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.fieldOwner;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;


/** Static backward data-flow analysis from one declared exception target. */
final class SeedBackwardStaticAnalyzer {
    private static final Logger LOG = LoggerFactory.getLogger(
            CausynthPipeline.class);
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
    /** Collection views backed by their receiver: mutating one mutates both. */
    private static final Set<String> BACKED_MAP_VIEWS = names(
            "entrySet", "keySet", "values", "navigableKeySet",
            "descendingKeySet");
    private static final Set<String> BACKED_ITERATORS = names(
            "iterator", "listIterator", "descendingIterator");
    /** Calls, by name, that write their receiver whatever its class: an
     *  application container's as much as a JDK one's (whose contract,
     *  JavaContainerTypes, names the rest). */
    private static final Set<String> CONTAINER_MUTATORS = names(
            "put", "putAll", "remove", "clear", "add", "addAll", "set",
            "replace", "compute", "computeIfAbsent", "computeIfPresent",
            "merge", "offer", "poll");
    private static final Set<String> COLLECTION_CONTRACT_OWNERS = names(
            "java.util.Collection", "java.util.List", "java.util.Set",
            "java.util.SortedSet", "java.util.NavigableSet",
            "java.util.Queue", "java.util.Deque");
    /** The one control-dependence row kind: branch operand -> guarded cell. */
    private static final String GUARD_KIND = "guard_dependency";
    private final CausynthTargetContext target;
    private final Map<String, SootClass> classesByName = new LinkedHashMap<>();
    private final Map<String, SootMethod> allMethodsBySignature =
            new LinkedHashMap<>();
    private final Map<String, List<Fact>> factsByMethod = new LinkedHashMap<>();
    /** Post-dominance per method: the ONE control-dependence rule. */
    private final Map<String, SiteControlDependence.MethodGuards>
            guardsByMethod = new LinkedHashMap<>();
    private final Map<String, List<FieldWrite>> fieldWritersByField =
            new LinkedHashMap<>();
    private final Map<String, List<Callsite>> constructorCallersByCallee =
            new LinkedHashMap<>();
    private final Map<String, List<Callsite>> methodCallersByCallee =
            new LinkedHashMap<>();
    /** The abstract types outside the scope that an application class runs
     *  a body of ({@link #buildGlobalStaticIndex}). */
    private final Set<String> dispatchOwners = new LinkedHashSet<>();
    /** Every application call site of the explicit boolean fault hook. */
    private final Map<String, List<Integer>> explicitFaultUnitsByMethod =
            new LinkedHashMap<>();
    /** Methods whose Jimple mentions one declared field. */
    private final Map<String, Set<String>> methodsReferencingField =
            new LinkedHashMap<>();
    private final Set<String> mutationIndexedFields = new LinkedHashSet<>();
    private final Map<String, Set<String>> relevantFieldEffectsByMethod =
            new LinkedHashMap<>();
    /** Per method, the relevant field cells it stores a constant into
     *  ({@link #expandStoreCallerGuards}). */
    private final Map<String, Set<String>> constantStoresByMethod =
            new LinkedHashMap<>();
    private final Map<String, Set<String>> relevantByMethod = new LinkedHashMap<>();
    private final Set<String> dirtyMethods = new LinkedHashSet<>();
    private final Set<String> selectedMethods =
            new DirtyMarkingSet(null);
    private final Map<EdgeIdentity, Map<String, Object>> emittedEdgeRows =
            new LinkedHashMap<>();
    private final Set<String> expandedDemands = new LinkedHashSet<>();
    private int discoveredExceptionSeedCount;
    /** Structural accessor per call signature; a cached null is a negative. */
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
    /* Identity-keyed, but Linked*: nothing iterates in identity-hash order. */
    private final Map<Fact, List<String>> localValueUsesCache =
            new LinkedHashMap<>();
    private final Map<Fact, List<String>> nonInvokeUsesCache =
            new LinkedHashMap<>();
    private final Map<Fact, List<String>> canonicalDefsCache =
            new LinkedHashMap<>();
    private final Map<Fact, List<String>> canonicalLocalUsesCache =
            new LinkedHashMap<>();
    private final WireFlowCatalog wireFlows;
    /** The ports {@link #deriveWirePort} found, by message field. */
    private final Map<String, WireFlowCatalog.WireFlow> derivedPorts =
            new LinkedHashMap<>();
    /** Which library calls are clocks ({@link #processLibraryReceiver}). */
    private final RootCatalog roots = new RootCatalog();
    /** Which out-of-scope classes are the system's own, not a library
     *  ({@link #processLibraryReceiver}); read at its first question. */
    private Predicate<String> systemClass;
    /** {@link #rpcMessages}, computed at the first demanded getter. */
    private Set<String> rpcMessages;
    /** The declared per-loop {@code K_L} (PIPELINE §2). */
    private final DeclaredLoopBodyBounds loopBodyBounds;
    private boolean globalStaticIndexBuilt;

    SeedBackwardStaticAnalyzer(CausynthTargetContext target) {
        this.target = target;
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            classesByName.put(sootClass.getName(), sootClass);
            for (SootMethod method : sootClass.getMethods()) {
                allMethodsBySignature.put(method.getSignature(), method);
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
            // A visitor that never answers visits the whole hierarchy.
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
        String targetMethod = target.exceptionTargetSite.methodSignature;
        SootMethod sootTarget = concreteMethod(targetMethod);
        if (sootTarget == null || !loadMethod(sootTarget)) {
            throw new IllegalStateException(
                    "Could not load declared target method: "
                            + targetMethod);
        }
        // Wire flows and fault hooks are seeds by declaration, even outside
        // the exception's value slice.
        buildGlobalStaticIndex();
        initializeExceptionSeedAnchors();
        seedDeclaredWireFlows();
        seedExplicitFaultEntries();
        runWorklist();
        if (discoveredExceptionSeedCount != 1) {
            throw new IllegalStateException("Declared exception target did "
                    + "not resolve to exactly one Jimple throw: "
                    + target.exceptionTargetSite.stableIdentity()
                    + "; matches=" + discoveredExceptionSeedCount);
        }
        planCommunicationCatalog(result);
        for (Map.Entry<String, List<FieldWrite>> field
                : fieldWritersByField.entrySet()) {
            List<String> sites = new ArrayList<>();
            for (FieldWrite write : field.getValue()) {
                sites.add(SiteId.of(write.method, write.unitIndex));
            }
            result.fieldWriters.put(field.getKey(), sites);
        }

        // Numbered in content order, not in the order the worklist found
        // them: the ids and the rows' order are the slice's, not the run's.
        List<EdgeIdentity> found = new ArrayList<>(emittedEdgeRows.keySet());
        Collections.sort(found);
        for (EdgeIdentity key : found) {
            Map<String, Object> edge = emittedEdgeRows.get(key);
            edge.put("id", "DF." + result.edges.size());
            result.edges.add(edge);
        }
        result.traceMethods.addAll(selectedMethods);
        Collections.sort(result.traceMethods);
        for (String method : result.traceMethods) {
            String authority = executionContextAuthority(method);
            if (!authority.isEmpty()) {
                result.executionContextAuthorities.put(method, authority);
            }
        }
        // Checked over the final plan only.
        loopBodyBounds.refuseUnclaimed(selectedMethods);
        return result;
    }

    /** The selected methods' port and loop catalog (SYMBOL-SCOPE §2.3). */
    private void planCommunicationCatalog(StaticProgram result) {
        List<String> selected = new ArrayList<>(selectedMethods);
        Collections.sort(selected);
        List<WireFlowCatalog.WireFlow> ports =
                new ArrayList<>(wireFlows.flows());
        ports.addAll(derivedPorts.values());
        CommunicationCatalogPlanner.Result discovered =
                CommunicationCatalogPlanner.plan(selected,
                        this::jimpleBody, ports, loopBodyBounds);
        // A pure function of the selected set: replace, never append.
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

    /** One method's Jimple body, or null. */
    private Body jimpleBody(String signature) {
        SootMethod method = concreteMethod(signature);
        return method == null ? null : activeBody(method);
    }

    /** Execution-context entry kind from Java concurrency contracts. */
    private String executionContextAuthority(String signature) {
        if (CausynthStaticFacts.constructor(signature)) {
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
                    "Declared target has no loaded Jimple body: " + method);
        }
        for (int throwIndex = 0; throwIndex < facts.size(); throwIndex++) {
            Fact throwFact = facts.get(throwIndex);
            if (declaredExceptionAllocation(facts, throwIndex) == null) {
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
            // Every branch on a path to the throw is in scope; which one
            // decides it is the scope map's TARGET_SITE row.
            forEachGuardOperand(method, throwFact, false,
                    (guardFact, node) -> {
                methodRelevant.add(node);
                addEdge("exception_guard", node, exceptionNode, method,
                        guardFact);
            });

            selectedMethods.add(method);
            discoveredExceptionSeedCount++;
        }
        LOG.info("Discovered {} direct throw sites for {} in {} methods",
                discoveredExceptionSeedCount, target.seedException,
                discoveredExceptionSeedCount == 0 ? 0 : 1);
    }

    /** Seeds every capture of every declared wire port. */
    private void seedDeclaredWireFlows() {
        for (WireFlowCatalog.WireFlow flow : wireFlows.flows()) {
            seedPort(flow);
        }
    }

    /**
     * Demands every capture of one port and joins each producer to each
     * consumer, so the slice continues on the sending side.  Idempotent: a
     * port that gains captures is seeded again.
     */
    private void seedPort(WireFlowCatalog.WireFlow flow) {
        List<String> producers = new ArrayList<>();
        List<Fact> producerFacts = new ArrayList<>();
        for (WireFlowCatalog.CaptureSite producer : flow.producers) {
            String node = seedCapture(flow, producer);
            Fact fact = captureFact(producer);
            producers.add(node);
            producerFacts.add(fact);
            if (WireFlowCatalog.CaptureSite.CALL_ARGUMENT.equals(
                    producer.kind)) {
                MethodSig callee = parseMethodSig(producer.callee);
                if (callee == null) {
                    throw new IllegalStateException(
                            "Could not resolve wire producer call: "
                                    + flow.id);
                }
                addEdge("wire_capture_argument", node,
                        formalParam(callee, producer.index),
                        producer.method, fact);
            }
        }
        for (WireFlowCatalog.CaptureSite consumer : flow.consumers) {
            String node = seedCapture(flow, consumer);
            Fact fact = captureFact(consumer);
            for (int index = 0; index < producers.size(); index++) {
                addEdge("wire_handoff", producers.get(index), node,
                        consumer.method,
                        fact == null ? producerFacts.get(index) : fact);
            }
        }
    }

    /** The field types a derived port carries: primitives and strings. */
    private static final Set<String> WIRE_LEAF_TYPES = names("boolean",
            "byte", "char", "short", "int", "long", "float", "double",
            "java.lang.String");

    /**
     * F3: a demanded {@code x = r.<M: T getF()>()} on a protobuf message M
     * that an RPC carries ({@link #rpcMessages}) reads a value another
     * process wrote through {@code M$Builder.setF(T)}.  The call is a
     * consumer of port (M, F), every call of that setter in the analysed
     * program is a producer, and each producer's argument is demanded in
     * turn, so the slice continues on the sending side.  Only demanded
     * getters derive, so the ports stay few; a capture a declared row holds
     * is that row's.
     */
    private void deriveWirePort(String method, Fact fact, MethodSig getter,
                                List<String> defs, Set<String> relevant) {
        if (!getter.params.isEmpty() || !getter.name.startsWith("get")
                || getter.name.length() == "get".length()
                || !WIRE_LEAF_TYPES.contains(getter.returnType)
                || !exactIntersects(relevant, defs)
                || !rpcMessages().contains(getter.owner)) {
            return;
        }
        WireFlowCatalog.CaptureSite consumer =
                WireFlowCatalog.CaptureSite.call(method,
                        WireFlowCatalog.CaptureSite.CALL_RETURN, -1,
                        getter.raw, fact.unitIndex, getter.returnType);
        if (wireFlows.captures(consumer)) return;
        WireFlowCatalog.WireFlow port = memoized(derivedPorts,
                getter.owner + "." + getter.name.substring(3),
                identity -> derivedPort(identity, getter));
        if (port.producers.isEmpty()) return;
        if (!port.captures(consumer)) port.consumers.add(consumer);
        seedPort(port);
    }

    /** Port (M, F), named {@code auto:<M's simple name>.<F>}, with its
     *  producers: every call of {@code M$Builder.setF(T)}, argument 0. */
    private WireFlowCatalog.WireFlow derivedPort(String identity,
                                                 MethodSig getter) {
        String message = getter.owner;
        String field = getter.name.substring(3);
        WireFlowCatalog.WireFlow port = new WireFlowCatalog.WireFlow(
                "auto:" + message.substring(Math.max(message.lastIndexOf('.'),
                        message.lastIndexOf('$')) + 1) + "." + field,
                identity, getter.returnType);
        String builder = message + "$Builder";
        String setter = "<" + builder + ": " + builder + " set" + field + "("
                + getter.returnType + ")>";
        buildGlobalStaticIndex();
        for (Callsite call : methodCallersByCallee.getOrDefault(setter,
                Collections.<Callsite>emptyList())) {
            WireFlowCatalog.CaptureSite producer =
                    WireFlowCatalog.CaptureSite.call(call.method,
                            WireFlowCatalog.CaptureSite.CALL_ARGUMENT, 0,
                            setter, call.unitIndex, getter.returnType);
            if (!wireFlows.captures(producer)) port.producers.add(producer);
        }
        return port;
    }

    /**
     * The protobuf messages that cross a process through a door: the
     * request and response of every protobuf service method -- a method
     * whose first parameter is the runtime's {@code RpcController}, the
     * shape protoc emits for an {@code rpc}, which a system's RPC engine
     * proxies on the client and dispatches on the server, so each call
     * passes its transport's door -- and every message a field of one holds
     * (an instance method's message return: a field getter, singular or
     * repeated), which the RPC carries inside it.  A message no service
     * reaches (an on-disk image section, an edit-log record, a streamed op)
     * is written to a file or a socket with no door and is none.  The
     * services are those of the loaded program: Soot resolves the analysis
     * scope's references transitively.
     */
    private Set<String> rpcMessages() {
        if (rpcMessages != null) return rpcMessages;
        List<String> pending = new ArrayList<>();
        for (SootClass type : Scene.v().getClasses()) {
            if (type.resolvingLevel() < SootClass.SIGNATURES) continue;
            for (SootMethod method : type.getMethods()) {
                if (method.getParameterCount() > 1 && method
                        .getParameterType(0).toString()
                        .endsWith(".protobuf.RpcController")) {
                    pending.add(method.getParameterType(1).toString());
                    pending.add(method.getReturnType().toString());
                }
            }
        }
        Set<String> found = new LinkedHashSet<>();
        while (!pending.isEmpty()) {
            String name = pending.remove(pending.size() - 1);
            if (found.contains(name) || !protobufMessage(name)) continue;
            found.add(name);
            for (SootMethod method : sceneClass(name).getMethods()) {
                if (!method.isStatic()) {
                    pending.add(method.getReturnType().toString());
                }
            }
        }
        LOG.info("{} protobuf message types cross a process by RPC",
                found.size());
        return rpcMessages = found;
    }

    /**
     * A generated protobuf message: its hierarchy reaches the runtime's
     * GeneratedMessage or GeneratedMessageV3 in whatever package a build
     * relocates protobuf to (Hadoop's org.apache.hadoop.thirdparty.protobuf).
     */
    private boolean protobufMessage(String className) {
        SootClass type = sceneClass(className);
        if (type == null) return false;
        for (String name : hierarchyNames(type)) {
            if (name.endsWith(".protobuf.GeneratedMessage")
                    || name.endsWith(".protobuf.GeneratedMessageV3")) {
                return true;
            }
        }
        return false;
    }

    /** A protobuf builder's field setter, {@code B B.setF(T)} of a nested
     *  {@code $Builder}: its calls are a derived port's producers wherever
     *  the message is ({@link #derivedPort}). */
    private static boolean builderSetter(MethodSig sig) {
        return sig.name.startsWith("set") && sig.params.size() == 1
                && sig.owner.endsWith("$Builder")
                && sig.owner.equals(sig.returnType);
    }

    /** Loads one capture's method and demands its value there. */
    private String seedCapture(WireFlowCatalog.WireFlow flow,
                               WireFlowCatalog.CaptureSite site) {
        if (!ensureLoaded(concreteMethod(site.method))) {
            throw new IllegalStateException("Could not load wire flow "
                    + "capture: " + flow.id + " at " + site.method);
        }
        Fact fact = captureFact(site);
        String node = captureNode(site, fact);
        if (node.isEmpty()) {
            throw new IllegalStateException(
                    "Could not resolve wire flow capture: " + flow.id
                            + " at " + site.siteId());
        }
        relevant(site.method).add(node);
        selectedMethods.add(site.method);
        return node;
    }

    /**
     * Seeds every explicit fault marker's destination as a root, so its
     * consumers and guards are kept by the ordinary control-dependence rule.
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
                // An ignored marker result stays a (branch-less) site.
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

                    demandControllingGuards(method, fact,
                            relevant(method),
                            Collections.singletonList(destination));
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

    private Fact declaredExceptionAllocation(
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
        // The ordinal is the class file's (ExceptionTargetLineResolver): a
        // door's woven construction is not the program's.
        int ordinal = 0;
        for (Fact candidate : facts) {
            if (DoorWeave.isWoven(candidate.unit)
                    || !target.seedException.equals(
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

    /** One method's CFG relation, built once. */
    private SiteControlDependence.MethodGuards cfgRelation(String method) {
        return memoized(guardsByMethod, method,
                SiteControlDependence.MethodGuards::of);
    }

    /**
     * Adds the operands of every branch deciding whether {@code site} runs.
     * The whole of control dependence in the slice, published as the one
     * {@link #GUARD_KIND} row kind.
     *
     * @return whether any branch decides it
     */
    private boolean demandControllingGuards(String method, Fact site,
                                            Set<String> relevant,
                                            Collection<String> guardedCells) {
        boolean[] guarded = {false};
        forEachGuardOperand(method, site, true, (guardFact, guardNode) -> {
            for (String cell : guardedCells) {
                addEdge(GUARD_KIND, guardNode, cell, method, guardFact);
            }
            relevant.add(guardNode);
            guarded[0] = true;
        });
        return guarded[0];
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
        // Monotone fixed point over finite cells.
        while (!dirtyMethods.isEmpty()) {
            String method = dirtyMethods.iterator().next();
            dirtyMethods.remove(method);
            if (!selectedMethods.contains(method)) {
                continue;
            }
            processMethod(method);
            expandThrows(method);
            expandDispatchCallers(method);
            expandFieldWriters(method);
            expandConstructorCallers(method);
            expandMethodCallers(method);
            expandStoreCallerGuards(method);
        }
    }

    private void processMethod(String method) {
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null) {
            return;
        }
        Set<String> relevant = relevant(method);
        MethodSig methodSig = parseMethodSig(method);
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
            boolean useExactHit = exactIntersects(relevant, uses);
            if (defExactHit) {
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

            if (defExactHit && !fact.isBranch) {
                // A demanded definition demands the branches deciding it.
                List<String> relevantDefs = new ArrayList<>();
                for (String def : defs) {
                    if (relevant.contains(def) && !ignoreNode(def)) {
                        relevantDefs.add(def);
                    }
                }
                if (!relevantDefs.isEmpty()) {
                    demandControllingGuards(method, fact, relevant,
                            relevantDefs);
                }
            }

            if (fact.isBranch && useExactHit) {
                for (String use : uses) {
                    addEdge(GUARD_KIND, use, factNode(fact), method, fact);
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
        if (!affectedRelevantHeapCells.isEmpty()) {
            // A heap write may have no relevant def local to hang guards on.
            demandControllingGuards(method, fact, relevant,
                    affectedRelevantHeapCells);
        }
    }

    /** Keeps array contents in the slice; the index never turns symbolic. */
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
        if (fact.unit instanceof AssignStmt
                && ((AssignStmt) fact.unit).getRightOp() instanceof Constant) {
            constantStoresByMethod.computeIfAbsent(method,
                    DirtyMarkingSet::new).add(fieldNode);
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
                        .computeIfAbsent(writer.method, DirtyMarkingSet::new)
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
        // Only this constructor's own call sites.
        if (thisRelevant || params.stream().anyMatch(
                param -> method.equals(param.constructor))) {
            forEachCallsite(constructorCallersByCallee, method,
                    (callsite, callsiteFact) -> expandCallerReceiver(
                            "CONSTRUCTOR_CALLER_RECEIVER",
                            "constructor_receiver", method, thisNode,
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
                markDirty(callsite.method);
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
        boolean paramRelevant = false;
        for (int i = 0; i < callee.params.size(); i++) {
            paramRelevant |= calleeRelevant.contains(formalParam(callee, i));
        }
        if (!paramRelevant && !thisRelevant) {
            return;
        }

        buildGlobalStaticIndex();
        forEachCallsite(methodCallersByCallee, method,
                (callsite, callsiteFact) -> {
            expandCallerArguments("METHOD_CALLER_PARAM", "caller_argument",
                    "method_caller_literal_argument", method, method, callee,
                    callsite, callsiteFact);
            addReceiverFieldEffectPathGuards(method,
                    callsite, callsiteFact, relevant(callsite.method));
            if (thisRelevant) {
                expandCallerReceiver("METHOD_CALLER_RECEIVER",
                        "method_receiver", method, thisNode, callsite,
                        callsiteFact);
            }
        });
    }

    /** How many calls up a constant store's callers' guards are sliced. */
    private static final int STORE_CALLER_DEPTH = 3;

    /**
     * A constant store carries no data: its cause is the branches that let
     * it run -- those of its own method ({@link #processFieldWrites}) and
     * those of the calls into its method, {@link #STORE_CALLER_DEPTH} calls
     * up, a virtual call included (SOLR-18406: Lucene's
     * CommitPoint.delete() sets {@code deleted = true}, and Solr's deletion
     * policy calls it through IndexCommit.delete() only when the commit's
     * reservation, a clock, has run out).  Each call's deciding operands are
     * demanded in its method, guarding the stored cells, and a dispatched
     * call links its caller to the method it runs.
     */
    private void expandStoreCallerGuards(String method) {
        Set<String> stored = constantStoresByMethod.get(method);
        if (stored == null || stored.isEmpty()) {
            return;
        }
        buildGlobalStaticIndex();
        Set<String> visited = new LinkedHashSet<>();
        List<String> level = Collections.singletonList(method);
        for (int depth = 0; depth < STORE_CALLER_DEPTH && !level.isEmpty();
             depth++) {
            List<String> next = new ArrayList<>();
            for (String callee : level) {
                if (!visited.add(callee)) continue;
                List<String> declared = new ArrayList<>();
                declared.add(callee);
                declared.addAll(resolveDispatchSources(callee));
                for (String target : declared) {
                    forEachCallsite(methodCallersByCallee, target,
                            (callsite, callsiteFact) -> {
                        // Once per callee and call, and again whenever the
                        // stored set has grown.
                        if (!expandOnce("STORE_CALLER_GUARDS", method,
                                stored.size(), callee, callsite.method,
                                callsiteFact.unitIndex)) {
                            return;
                        }
                        loadMethod(concreteMethod(callsite.method));
                        selectedMethods.add(callsite.method);
                        if (!target.equals(callee)) {
                            addEdge("dispatch_activation",
                                    factNode(callsiteFact),
                                    callee + ".activation", callsite.method,
                                    callsiteFact);
                        }
                        demandControllingGuards(callsite.method, callsiteFact,
                                relevant(callsite.method), stored);
                        next.add(callsite.method);
                    });
                }
            }
            level = next;
        }
    }

    private void selectActivationCaller(String kind, String targetMethod,
                                        String callerMethod, Fact callsite) {
        if (callerMethod == null || callsite == null
                || !expandOnce(kind, targetMethod, callerMethod,
                callsite.unitIndex)) {
            return;
        }
        loadMethod(concreteMethod(callerMethod));
        String activation = targetMethod + ".activation";
        addEdge(kind, factNode(callsite), activation, callerMethod,
                callsite);
        selectedMethods.add(callerMethod);

        demandControllingGuards(callerMethod, callsite,
                relevant(callerMethod),
                Collections.singletonList(activation));
    }

    /**
     * Emits a typed literal a caller passes for a relevant formal; answers
     * whether it was one (its caller joins the slice).
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

    /** The guards of a relevant field-writing call decide its effect. */
    private void addReceiverFieldEffectPathGuards(
            String calleeMethod, Callsite callsite, Fact callsiteFact,
            Set<String> callerRelevant) {
        Set<String> effectFields = relevantFieldEffectsByMethod.get(
                calleeMethod);
        if (effectFields != null && !effectFields.isEmpty()
                && demandControllingGuards(callsite.method, callsiteFact,
                callerRelevant, effectFields)) {
            selectedMethods.add(callsite.method);
        }
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

    /** Builds the reverse application index once, on first demand. */
    private void buildGlobalStaticIndex() {
        if (globalStaticIndexBuilt) {
            return;
        }
        long startedAt = System.nanoTime();
        int indexedMethods = 0;
        int indexedFacts = 0;
        globalStaticIndexBuilt = true;
        // A call through an abstract type an application class runs a body
        // of is a call into the application, whatever scope the type is in:
        // Solr's IndexCommit.delete() runs Lucene's CommitPoint.delete().
        for (SootClass sootClass : classesByName.values()) {
            for (String name : hierarchyNames(sootClass)) {
                SootClass type = sceneClass(name);
                if (type != null && !type.isApplicationClass()
                        && !skipDispatchOwner(name)
                        && (type.isInterface() || type.isAbstract())) {
                    dispatchOwners.add(name);
                }
            }
        }
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
                boolean constructor = sig != null && "<init>".equals(sig.name);
                if (sig != null && (isApplicationClassName(sig.owner)
                        || !constructor && dispatchOwners.contains(sig.owner)
                        || builderSetter(sig))) {
                    String unitText = unit.toString();
                    String receiver = canonical(methodSignature,
                            invokeBaseLocal(unitText));
                    List<String> actuals = canonicalPositionList(
                            methodSignature, actualInvokeArgs(unitText));
                    if (constructor) {
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
            loadMethod(concreteMethod(method));
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
    private static void addIndexedCallsite(Map<String, List<Callsite>> index,
                                           String callee, Callsite callsite) {
        index.computeIfAbsent(callee, ignored -> new ArrayList<>())
                .add(callsite);
    }

    /**
     * Resolves backed collection mutations lazily, per demanded field.  Exact:
     * {@link #fieldsAliasedByLocal} only returns fields its method references.
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
        // The base of an instance-field store is a use box, not a value.
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

    /** Only java.util APIs specified to return a receiver-backed view. */
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

    /** Whether a call writes its receiver: a container mutation, by name
     *  or by its JDK contract, or a write of a JDK atomic's value. */
    private boolean isFieldMutator(Fact fact) {
        MethodSig sig = parseMethodSig(fact.invoke);
        return sig != null && (CONTAINER_MUTATORS.contains(sig.name)
                || JavaContainerTypes.mutation(sig.raw,
                this::libraryHierarchy)
                || SharedFieldFlow.atomicWrite(sig.raw));
    }

    /**
     * A library class's supertypes, itself included: they decide which
     * container contract a call on it states (JavaContainerTypes, by
     * interface).  None for an application class, whose calls run the body
     * the slice follows.
     */
    private Collection<String> libraryHierarchy(String className) {
        SootClass type = isApplicationClassName(className) ? null
                : sceneClass(className);
        return type == null ? Collections.<String>emptySet()
                : hierarchyNames(type);
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
        deriveWirePort(callerMethod, fact, callee, defs, callerRelevant);
        processSemanticContainerOperation(callerMethod, fact,
                callee, defs, callerRelevant);
        processSemanticContainerMutation(callerMethod, fact,
                callee, callerRelevant);
        processAccessorInvoke(callerMethod, fact, callee, defs,
                callerRelevant);
        processLibraryReceiver(callerMethod, fact, callee, defs,
                callerRelevant);
        List<String> actuals = canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText));
        processContainerCallMutationEffects(callerMethod, fact, callee,
                actuals, callerRelevant);
        processConstructorObjectInvoke(callerMethod, fact, callee,
                actuals, callerRelevant);
        boolean dynamicDispatch = !resolveDispatchTargets(callee)
                .isEmpty();
        boolean containerQuery = JavaContainerTypes.query(
                callee.raw, this::libraryHierarchy);
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
            if (!containerQuery) {
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

    /** One forward argument walk for an ordinary Java call. */
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
            addEdge(kind, actual, formal, callerMethod, fact);
            callerRelevant.add(actual);
        }
        return relevantFlow;
    }

    /** The same walk over a call's returned value. */
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
            addEdge(kind, returnNode, def, callerMethod, fact);
            if (targetExpandable) {
                targetRelevant.add(returnNode);
                selectedMethods.add(targetMethod);
            }
        }
    }

    /**
     * A container query's result depends on its receiver and arguments
     * (library receivers are otherwise excluded), by the contract of the
     * receiver's interface (JavaContainerTypes), a stream pipeline's and a
     * static {@code Collectors} call's included; a functional argument
     * contributes its functional method's return ({@link
     * #enterFunctionalArguments}).  Value semantics belong to the VM's
     * {@code ContainerRelation}.
     */
    private void processSemanticContainerOperation(
            String callerMethod, Fact fact, MethodSig callee,
            List<String> defs, Set<String> callerRelevant) {
        if (defs.isEmpty()
                || !(JavaContainerTypes.query(callee.raw,
                this::libraryHierarchy) || containerArray(callee))) {
            return;
        }
        List<String> relevantDefs = new ArrayList<>();
        for (String def : defs) {
            if (!ignoreNode(def) && callerRelevant.contains(def)) {
                relevantDefs.add(def);
            }
        }
        if (relevantDefs.isEmpty()) return;

        // A static call (Collectors.toList()) reads its arguments alone.
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver != null) {
            String receiverNode = canonical(callerMethod, receiver);
            if (ignoreNode(receiverNode)) return;
            // The result is demanded, so the receiver's state is a value
            // input.
            for (String def : relevantDefs) {
                Map<String, Object> edge = addEdge("container_receiver",
                        receiverNode, def, callerMethod, fact);
                if (edge != null) {
                    edge.put("dependencyRole",
                            DependencyRole.VALUE_FRONTIER);
                }
            }
            callerRelevant.add(receiverNode);
        }

        for (String argument : canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText))) {
            if (ignoreNode(argument)) continue;
            for (String def : relevantDefs) {
                addEdge("container_argument", argument, def,
                        callerMethod, fact);
            }
            callerRelevant.add(argument);
        }
        enterFunctionalArguments(callerMethod, fact);
    }

    /** A functional object's interfaces: java.util.function's, and a
     *  Comparator. */
    private static boolean functionalInterface(String name) {
        return name.startsWith("java.util.function.")
                || "java.util.Comparator".equals(name);
    }

    /**
     * Each functional argument of a container or stream call the slice
     * demands contributes its functional method's return (SYMBOL-SCOPE
     * §2.2): one {@code functional_return} edge from that method's return to
     * the argument, and the slice enters the method -- each method of the
     * object's class implementing an abstract method of a functional
     * interface it implements.  The class is the one the argument is created
     * from: a {@code new C}, or a static factory of a functional class (the
     * {@code bootstrap$} of Soot's desugared lambda or method reference).
     * The values it captured reach the factory's arguments at the creation
     * site through the constructor-object edges.  An argument read from a
     * field or a parameter states no class and is entered nowhere.
     */
    private void enterFunctionalArguments(String callerMethod, Fact fact) {
        List<Value> arguments = ((Stmt) fact.unit).getInvokeExpr().getArgs();
        List<String> nodes = canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText));
        for (int index = 0; index < arguments.size()
                && index < nodes.size(); index++) {
            if (!(arguments.get(index) instanceof Local)
                    || ignoreNode(nodes.get(index))) {
                continue;
            }
            for (SootClass created : creationClasses(callerMethod,
                    (Local) arguments.get(index))) {
                for (SootMethod method : functionalMethods(created)) {
                    String signature = method.getSignature();
                    if (!isExpandableMethod(signature)) continue;
                    loadMethod(method);
                    String returned = signature + ".return";
                    addEdge("functional_return", returned,
                            nodes.get(index), callerMethod, fact);
                    relevant(signature).add(returned);
                    selectedMethods.add(signature);
                }
            }
        }
    }

    /** The classes a local's definitions create its object of: a {@code
     *  new C}, or a static method of a functional class C (its factory). */
    private Set<SootClass> creationClasses(String method, Local local) {
        Set<SootClass> classes = new LinkedHashSet<>();
        for (Fact fact : factsByMethod.get(method)) {
            if (!(fact.unit instanceof AssignStmt)
                    || ((AssignStmt) fact.unit).getLeftOp() != local) {
                continue;
            }
            Value created = ((AssignStmt) fact.unit).getRightOp();
            SootClass type = created instanceof NewExpr
                    ? ((NewExpr) created).getBaseType().getSootClass()
                    : created instanceof soot.jimple.StaticInvokeExpr
                    ? ((InvokeExpr) created).getMethodRef()
                    .getDeclaringClass() : null;
            // Only the analysed scope's classes have a method to enter.
            if (type != null && type.isApplicationClass()
                    && !functionalMethods(type).isEmpty()) {
                classes.add(type);
            }
        }
        return classes;
    }

    /** The methods a class (or a superclass) implements of the abstract
     *  methods of the functional interfaces it implements. */
    private List<SootMethod> functionalMethods(SootClass type) {
        List<SootMethod> methods = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (SootClass owner = type; owner != null
                && owner.resolvingLevel() >= SootClass.HIERARCHY;
             owner = owner.hasSuperclass() ? owner.getSuperclass() : null) {
            Deque<SootClass> interfaces = new ArrayDeque<>(
                    owner.getInterfaces());
            while (!interfaces.isEmpty()) {
                SootClass contract = interfaces.removeFirst();
                if (!seen.add(contract.getName())
                        || contract.resolvingLevel() < SootClass.HIERARCHY) {
                    continue;
                }
                interfaces.addAll(contract.getInterfaces());
                if (!functionalInterface(contract.getName())
                        || contract.resolvingLevel()
                        < SootClass.SIGNATURES) {
                    continue;
                }
                for (SootMethod declared : contract.getMethods()) {
                    if (!declared.isAbstract() || declared.isStatic()) {
                        continue;
                    }
                    SootMethod implementation = implementation(type,
                            declared.getSubSignature());
                    if (implementation != null
                            && !methods.contains(implementation)) {
                        methods.add(implementation);
                    }
                }
            }
        }
        return methods;
    }

    /** The concrete method a class runs for one subsignature: its own or
     *  its nearest superclass's; null when none states one. */
    private static SootMethod implementation(SootClass type,
                                             String subSignature) {
        for (SootClass owner = type; owner != null
                && owner.resolvingLevel() >= SootClass.SIGNATURES;
             owner = owner.hasSuperclass() ? owner.getSuperclass() : null) {
            SootMethod method = owner.getMethodUnsafe(subSignature);
            if (method != null && method.isConcrete()) return method;
        }
        return null;
    }

    /**
     * Mutation counterpart of {@link #processSemanticContainerOperation}: a
     * relevant container receiver demands its mutators' arguments, and the
     * fields it is later published into name the mutation a write of theirs
     * ({@link #publishMutation}).
     */
    private void processSemanticContainerMutation(
            String callerMethod, Fact fact, MethodSig callee,
            Set<String> callerRelevant) {
        if (!JavaContainerTypes.mutation(callee.raw,
                this::libraryHierarchy)) {
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
        enterFunctionalArguments(callerMethod, fact);
        publishMutation(callerMethod, fact, receiver);
    }

    /**
     * P2(b) (R3-REFCONT): a mutation of the container a local holds shapes
     * the referent every later store of that local -- or of a copy of it,
     * before it is redefined -- publishes into a field, and, one call up,
     * the referent the method returns into each field its callers store
     * the result into.  One {@code container_publication} edge per field,
     * from the local ({@code publishedFrom}) to the field at the mutation:
     * the scope map's write site of that field with the mutation's guards.
     * solr-18406: {@code updateKnownCommitPoints} puts each commit whose
     * {@code !wrapper.isDeleted()} holds into a fresh map, then stores the
     * map into {@code knownCommits}.  A mutation of a field's container
     * through an alias is {@link #fieldsAliasedByLocal}'s.
     */
    private void publishMutation(String method, Fact mutation, String local) {
        if (!expandOnce("PUBLICATION", method, mutation.unitIndex)) return;
        Set<String> fields = new LinkedHashSet<>();
        if (storedFrom(factsByMethod.get(method), mutation.unitIndex, local,
                fields)) {
            buildGlobalStaticIndex();
            List<String> declared = new ArrayList<>();
            declared.add(method);
            declared.addAll(resolveDispatchSources(method));
            for (String callee : declared) {
                forEachCallsite(methodCallersByCallee, callee,
                        (callsite, call) -> {
                    if (call.unit instanceof AssignStmt
                            && ((AssignStmt) call.unit).getLeftOp()
                            instanceof Local) {
                        storedFrom(factsByMethod.get(callsite.method),
                                call.unitIndex, ((Local) ((AssignStmt)
                                        call.unit).getLeftOp()).getName(),
                                fields);
                    }
                });
            }
        }
        for (String field : fields) {
            Map<String, Object> edge = addEdge("container_publication",
                    canonical(method, local), field, method, mutation);
            if (edge != null) edge.put("publishedFrom", local);
        }
    }

    /**
     * Adds to {@code fields} each field a fact after {@code index} stores
     * {@code local}, or a copy of it, into, up to its redefinition.
     *
     * @return whether the method returns it
     */
    private static boolean storedFrom(List<Fact> facts, int index,
                                      String local, Set<String> fields) {
        Set<String> aliases = new LinkedHashSet<>();
        aliases.add(local);
        boolean returned = false;
        for (int at = index + 1; facts != null && at < facts.size()
                && !aliases.isEmpty(); at++) {
            Unit unit = facts.get(at).unit;
            if (unit instanceof ReturnStmt) {
                returned |= alias(((ReturnStmt) unit).getOp(), aliases);
                continue;
            }
            if (!(unit instanceof AssignStmt)) continue;
            Value target = ((AssignStmt) unit).getLeftOp();
            boolean copy = alias(((AssignStmt) unit).getRightOp(), aliases);
            if (target instanceof FieldRef) {
                if (copy) {
                    fields.add(CausynthStaticFacts.declaredFieldSignature(
                            ((FieldRef) target).getFieldRef()));
                }
            } else if (target instanceof Local) {
                if (copy) {
                    aliases.add(((Local) target).getName());
                } else {
                    aliases.remove(((Local) target).getName());
                }
            }
        }
        return returned;
    }

    /** Whether {@code value}, through a cast, is one of the locals. */
    private static boolean alias(Value value, Set<String> locals) {
        Value operand = value instanceof CastExpr
                ? ((CastExpr) value).getOp() : value;
        return operand instanceof Local
                && locals.contains(((Local) operand).getName());
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
                if (!JavaContainerTypes.mutation(fact.invoke,
                        this::libraryHierarchy)) {
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

    /** A collection's {@code toArray}: an array of its elements, so it
     *  depends on the collection's state as a query's result does. */
    private static boolean containerArray(MethodSig method) {
        return COLLECTION_CONTRACT_OWNERS.contains(method.owner)
                && "toArray".equals(method.name)
                && method.returnType.endsWith("[]")
                && (method.params.isEmpty()
                || (method.params.size() == 1
                && method.params.get(0).endsWith("[]")));
    }

    /** A demanded new object depends on its constructor arguments. */
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
        if (defs.isEmpty()) {
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

    /**
     * A demanded result of any other library call depends on its receiver's
     * state when the receiver is shared ({@link LibraryReceivers}): one
     * {@code library_receiver} row from the receiver to each demanded def.
     * Application calls, container contracts, value types, accessors and
     * dispatched calls state their dependence themselves, a clock's value is
     * a root whatever its receiver holds, and a call into the system's own
     * code outside the scope is the scope frontier's.
     */
    private Predicate<String> systemClass() {
        if (systemClass == null) {
            systemClass = LibraryReceivers.systemClasses(
                    System.getProperty(LibraryReceivers.ROOTS));
        }
        return systemClass;
    }

    private void processLibraryReceiver(String callerMethod, Fact fact,
                                        MethodSig callee, List<String> defs,
                                        Set<String> callerRelevant) {
        List<String> demanded = new ArrayList<>();
        for (String def : defs) {
            if (!ignoreNode(def) && callerRelevant.contains(def)) {
                demanded.add(def);
            }
        }
        InvokeExpr call = ((Stmt) fact.unit).getInvokeExpr();
        if (demanded.isEmpty() || !(call instanceof InstanceInvokeExpr)
                || "<init>".equals(callee.name)
                || isApplicationClassName(callee.owner)
                || systemClass().test(callee.owner)
                || isValueLikeLibraryInvoke(callee)
                || JavaContainerTypes.query(callee.raw, this::libraryHierarchy)
                || JavaContainerTypes.mutation(callee.raw,
                this::libraryHierarchy)
                || containerArray(callee)
                || structuralFieldAccessor(callee) != null
                || !resolveDispatchTargets(callee).isEmpty()
                || !LibraryReceivers.stateful(callee.owner, callee.name)
                || roots.clock(callee.raw)) {
            return;
        }
        Value base = ((InstanceInvokeExpr) call).getBase();
        List<Unit> units = new ArrayList<>();
        for (Fact each : factsByMethod.get(callerMethod)) units.add(each.unit);
        if (!(base instanceof Local) || !LibraryReceivers.shared(units,
                fact.unitIndex, (Local) base, invoked -> structuralFieldAccessor(
                        parseMethodSig(invoked.getMethodRef().getSignature()))
                        != null)) {
            return;
        }
        String receiver = canonical(callerMethod, base.toString());
        for (String def : demanded) {
            Map<String, Object> edge = addEdge("library_receiver", receiver,
                    def, callerMethod, fact);
            if (edge != null) {
                edge.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
            }
        }
        callerRelevant.add(receiver);
    }

    private void annotateAccessorDeclaredFieldEdge(
            Map<String, Object> edge, SootField field, String accessor) {
        if (edge == null) {
            return;
        }
        edge.put("declaredFieldSignature", field.getSignature());
        edge.put("accessorImplementationMethod", accessor);
    }

    /** Attaches the resolved declaration to one direct field read. */
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

    /** The unique analyzable closed-world receiver of this call, or null. */
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

    /** A field accessor, recognized from its body, never its spelling. */
    private StructuralFieldAccessor structuralFieldAccessor(
            MethodSig callee) {
        if (callee == null) {
            return null;
        }
        if (structuralFieldAccessors.containsKey(callee.raw)) {
            return structuralFieldAccessors.get(callee.raw);
        }
        SootField atomic = StructuralFieldAccessorProof.atomicField(
                callee.raw);
        StructuralFieldAccessor resolved = atomic != null
                ? new StructuralFieldAccessor(callee.raw, atomic)
                : inspectStructuralFieldAccessor(callee,
                        uniqueAnalyzableImplementation(callee));
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
        return new StructuralFieldAccessor(method.getSignature(), field);
    }

    private void processDispatchInvoke(String callerMethod, Fact fact,
                                       MethodSig callee, List<String> defs,
                                       List<String> actuals,
                                       Set<String> callerRelevant) {
        List<String> targetMethods = resolveDispatchTargets(callee);
        if (targetMethods.isEmpty()) {
            return;
        }
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
            SootClass owner = sceneClass(callee.owner);
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

    /**
     * The concrete methods of the analysis scope a call on {@code
     * sig.owner} may run that {@code accept}s (CHA): for each concrete
     * subtype of the owner, the method its lookup finds, declared there or
     * inherited.  {@code
     * Replica.getGenerationStamp()} runs {@code Block}'s through {@code
     * ReplicaInfo extends Block implements Replica}, though {@code Block}
     * itself implements no {@code Replica}.
     */
    private List<SootMethod> concreteImplementations(
            MethodSig sig, Predicate<SootMethod> accept) {
        SootClass owner = sceneClass(sig.owner);
        String subSignature = methodSubSignature(sig);
        SootMethod declared = owner == null ? null
                : walkHierarchy(owner,
                        type -> type.getMethodUnsafe(subSignature));
        if (declared == null) return Collections.emptyList();
        List<SootMethod> matches = new ArrayList<>();
        for (SootMethod target : abstractDispatch(owner, declared)) {
            // The analysis scope's bodies only: a library body the Scene can
            // load is still outside what the slice follows.
            if (target.getDeclaringClass().isApplicationClass()
                    && accept.test(target)) {
                matches.add(target);
            }
        }
        return matches;
    }

    /** The concrete targets of {@code declared} below {@code owner}, by
     *  signature (the hierarchy answers a hash set of methods, in identity
     *  order); none when it cannot resolve them (a phantom supertype). */
    private static List<SootMethod> abstractDispatch(SootClass owner,
                                                     SootMethod declared) {
        List<SootMethod> targets;
        try {
            targets = new ArrayList<>(Scene.v().getOrMakeFastHierarchy()
                    .resolveAbstractDispatch(owner, declared));
        } catch (RuntimeException unresolved) {
            return Collections.emptyList();
        }
        targets.sort(Comparator.comparing(SootMethod::getSignature));
        return targets;
    }

    /** A loaded, non-phantom class by name, application or library. */
    private static SootClass sceneClass(String name) {
        SootClass found = Scene.v().getSootClassUnsafe(name, false);
        return found == null || found.isPhantom() ? null : found;
    }

    private List<String> applicationImplementationSignatures(MethodSig sig) {
        List<String> signatures = new ArrayList<>();
        for (SootMethod implementation : concreteImplementations(sig,
                method -> true)) {
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
        if (sourceMethods.isEmpty()) {
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
                boolean relevantFlow = expandCallerArguments(
                        "DISPATCH_CALLER_PARAM", "dispatch_caller_argument",
                        null, targetMethod, sourceMethod, targetSig,
                        callsite, callsiteFact);
                if (targetThisRelevant) {
                    relevantFlow |= expandCallerReceiver(
                            "DISPATCH_CALLER_RECEIVER",
                            "dispatch_caller_receiver", targetMethod,
                            targetThis, callsite, callsiteFact);
                }
                if (relevantFlow) {
                    selectActivationCaller("dispatch_activation",
                            targetMethod, callsite.method, callsiteFact);
                }
            });
        }
    }

    /**
     * The one call-site walk every caller expander takes, in index order;
     * expanders differ only in what they demand at a site.
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
     * At one call site, demands each actual whose formal is relevant.  A
     * literal actual is a typed-literal row of {@code literalKind}, or
     * nothing when that is null.
     *
     * @return whether an actual was demanded
     */
    private boolean expandCallerArguments(
            String demandKind, String edgeKind, String literalKind,
            String targetMethod, String demandScope, MethodSig target,
            Callsite callsite, Fact callsiteFact) {
        Set<String> targetRelevant = relevant(targetMethod);
        Set<String> callerRelevant = relevant(callsite.method);
        boolean expanded = false;
        int count = Math.min(callsite.actuals.size(), target.params.size());
        for (int index = 0; index < count; index++) {
            String formal = formalParam(target, index);
            if (!targetRelevant.contains(formal)
                    || !expandOnce(demandKind, targetMethod, demandScope,
                    index, callsite.method, callsite.unitIndex)) {
                continue;
            }
            String actual = callsite.actuals.get(index);
            if (ignoreNode(actual)) {
                if (literalKind != null && addTypedLiteralCallerArgument(
                        literalKind, target, index, callsite.method,
                        callsiteFact)) {
                    selectedMethods.add(callsite.method);
                }
                continue;
            }
            addEdge(edgeKind, actual, formal, callsite.method,
                    callsiteFact);
            callerRelevant.add(actual);
            selectedMethods.add(callsite.method);
            markDirty(callsite.method);
            expanded = true;
        }
        return expanded;
    }

    /** At one call site, demands the receiver of a relevant {@code this}. */
    private boolean expandCallerReceiver(
            String demandKind, String edgeKind, String targetMethod,
            String targetThis, Callsite callsite, Fact callsiteFact) {
        if (targetThis == null || ignoreNode(callsite.receiver)) {
            return false;
        }
        if (relevant(targetMethod).contains(targetThis)
                && expandOnce(demandKind, targetMethod,
                callsite.method, callsite.unitIndex)) {
            addEdge(edgeKind, callsite.receiver,
                    targetThis, callsite.method, callsiteFact);
            relevant(callsite.method).add(callsite.receiver);
            selectedMethods.add(callsite.method);
            markDirty(callsite.method);
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
            // The supertypes of every class that runs this body: its own
            // and those of each subtype inheriting it.
            for (SootClass runner : inheritingSubtypes(targetClass,
                    subSignature)) {
                for (String candidateName : hierarchyNames(runner)) {
                    SootClass candidate = sceneClass(candidateName);
                    if (candidate == null
                            || skipDispatchOwner(candidate.getName())
                            || (!candidate.isInterface()
                            && !candidate.isAbstract())) {
                        continue;
                    }
                    SootMethod method =
                            candidate.getMethodUnsafe(subSignature);
                    if (method != null) sources.add(method.getSignature());
                }
            }
            return sources.isEmpty() ? Collections.<String>emptyList()
                    : Collections.unmodifiableList(
                            new ArrayList<>(sources));
        });
    }

    /** {@code declaring} and each of its subclasses that inherits its
     *  {@code subSignature} (declares none of its own), breadth first, each
     *  level's subclasses by name (the hierarchy answers a hash set). */
    private static List<SootClass> inheritingSubtypes(SootClass declaring,
                                                      String subSignature) {
        List<SootClass> runners = new ArrayList<>();
        Deque<SootClass> work = new ArrayDeque<>();
        work.add(declaring);
        while (!work.isEmpty()) {
            SootClass type = work.removeFirst();
            if (type != declaring
                    && type.getMethodUnsafe(subSignature) != null) {
                continue;
            }
            runners.add(type);
            List<SootClass> subclasses = new ArrayList<>(Scene.v()
                    .getOrMakeFastHierarchy().getSubclassesOf(type));
            subclasses.sort(Comparator.comparing(SootClass::getName));
            work.addAll(subclasses);
        }
        return runners;
    }

    private boolean isExpandableMethod(String signature) {
        SootMethod method = concreteMethod(signature);
        MethodSig sig = parseMethodSig(signature);
        return method != null
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
     * Visits each canonical operand of each branch {@code site} depends on.
     * A call a door fault leaves for a handler is such a branch, and its
     * operand is where the fault comes from: the {@code .throws} cell of each
     * callee it escapes ({@link FaultPropagation}), demanded there.
     */
    private void forEachGuardOperand(
            String method, Fact site, boolean controllingOnly,
            BiConsumer<Fact, String> visit) {
        if (site == null || site.unitIndex < 0) return;
        for (Integer guardIndex : cfgRelation(method).reaching(
                site.unitIndex, controllingOnly)) {
            Fact guardFact = indexedFact(method, guardIndex.intValue());
            if (guardFact == null) continue;
            FaultPropagation.Raise raise = guardFact.isBranch ? null
                    : FaultPropagation.current().raise(method,
                    guardFact.unit);
            if (raise != null) {
                for (String origin : raise.callees) {
                    demandThrows(origin);
                    visit.accept(guardFact, origin);
                }
                continue;
            }
            for (String use : causalGuardUses(guardFact)) {
                String guardNode = canonical(method, use);
                if (!ignoreNode(guardNode)) {
                    visit.accept(guardFact, guardNode);
                }
            }
        }
    }

    /** Demands a method's {@code .throws} cell in that method. */
    private void demandThrows(String cell) {
        String method = cell.substring(0,
                cell.length() - FaultPropagation.THROWS.length());
        loadMethod(concreteMethod(method));
        relevant(method).add(cell);
        selectedMethods.add(method);
    }

    /**
     * A demanded {@code <m>.throws}: each raise a door fault escapes {@code
     * m} from ({@link FaultPropagation}) flows into it ({@code
     * exception_flow}) from its origins -- a woven throw's marker local, a
     * callee's {@code .throws} -- under the raise's own guards.
     */
    private void expandThrows(String method) {
        String cell = FaultPropagation.throwsCell(method);
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null || !relevant(method).contains(cell)
                || !expandOnce("THROWS", method)) {
            return;
        }
        Set<String> relevant = relevant(method);
        for (FaultPropagation.Raise raise
                : FaultPropagation.current().escapes(method)) {
            Fact fact = null;
            for (Fact candidate : facts) {
                if (candidate.unit == raise.unit) fact = candidate;
            }
            if (fact == null) continue;
            List<String> origins = new ArrayList<>(raise.callees);
            for (Local marker : raise.markers) {
                origins.add(canonical(method, marker.getName()));
            }
            for (String origin : origins) {
                addEdge("exception_flow", origin, cell, method, fact);
                if (origin.endsWith(FaultPropagation.THROWS)) {
                    demandThrows(origin);
                } else {
                    relevant.add(origin);
                }
            }
            demandControllingGuards(method, fact, relevant,
                    Collections.singletonList(cell));
        }
    }

    private boolean expandOnce(String kind, Object... identity) {
        StringBuilder key = new StringBuilder(kind);
        for (Object value : identity) {
            key.append('\n').append(String.valueOf(value));
        }
        return expandedDemands.add(key.toString());
    }

    /**
     * Processes a selected method again.  Any demand that grows is followed
     * by this for every method whose pass reads it: a caller when a callee's
     * demand reaches its actual (its own pass emits the call's {@code
     * call_argument} and dispatch rows from the callee's demand, even when
     * the actual was already relevant), a method whose field effects or
     * constant stores grew.  Otherwise the rows would depend on the order
     * the worklist met the methods.
     */
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
                // Use boxes hold a composite expression and its leaves.
                if (!atomicDataflowUse(use)
                        || (!valueLikeLibraryInvoke && use.equals(invokeBase))
                        || applicationInvokeArgs.contains(use)
                        || arrayStructureOperands.contains(use)
                        || isFieldAccessValue(use)) {
                    continue;
                }
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
        // A wrapper's own unboxing accessor, Boolean's included: solr-18413's
        // DocCollection.isReadOnly() unboxes its Boolean readOnly.
        if (JavaPrimitiveBoxing.unboxing(invoked.raw)) {
            return true;
        }
        String owner = invoked.owner;
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
                // Superclass before interfaces, as Java lookup does.
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
        // Only a guard may name one cell at both ends (x = f(x) if x...).
        boolean sameCellGuard = GUARD_KIND.equals(kind) && fact != null;
        if (ignoreNode(fromText) || ignoreNode(toText)
                || fromText.equals(toText) && !sameCellGuard) {
            return null;
        }
        EdgeIdentity key = edgeKey(kind, fromText, toText, method, fact);
        Map<String, Object> edge = emittedEdgeRows.get(key);
        if (edge == null) {
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
                    // Numbered by analyze() once the slice is complete.
                    "id", "",
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
                if (fact.invoke != null) {
                    edge.put("invoke", fact.invoke);
                }
            }
            emittedEdgeRows.put(key, edge);
        }
        return edge;
    }

    /** Whether a {@code local_def_use} row is an exact JVM value copy. */
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

    /** A call that is one read of one field: the method that answers it
     *  (its body's proof, or a JDK atomic's table entry), and the field. */
    private static final class StructuralFieldAccessor {
        private final String implementation;
        private final SootField field;

        private StructuralFieldAccessor(String implementation,
                                        SootField field) {
            this.implementation = implementation;
            this.field = field;
        }
    }

    /** One emitted edge's identity: kind, ends, method and unit; ordered by
     *  method, unit, kind and ends. */
    private static final class EdgeIdentity
            implements Comparable<EdgeIdentity> {
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
        public int compareTo(EdgeIdentity other) {
            int order = method.compareTo(other.method);
            if (order == 0) order = Integer.compare(unitIndex, other.unitIndex);
            if (order == 0) {
                order = Boolean.compare(concreteSite, other.concreteSite);
            }
            if (order == 0) order = kind.compareTo(other.kind);
            if (order == 0) order = from.compareTo(other.from);
            return order == 0 ? to.compareTo(other.to) : order;
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
        return unitIndex >= 0 ? SiteId.of(method, unitIndex)
                : method + "#synthetic:" + firstNonBlank(kind, "edge");
    }

    private static Set<String> names(String... values) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(values)));
    }

}
