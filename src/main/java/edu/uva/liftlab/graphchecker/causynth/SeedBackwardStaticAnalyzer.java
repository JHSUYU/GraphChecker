package edu.uva.liftlab.graphchecker.causynth;

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
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.UnitGraph;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
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
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.CallbackRegistration;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ConstructorCallsite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ConstructorParam;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ExceptionConstruction;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.ExceptionGuard;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.Fact;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.FieldWrite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.InstanceFieldAccess;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.MappedEndpoint;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.MethodCallsite;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.RpcTarget;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.SeedLookupAnchor;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.StaticPortMapping;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.actualInvokeArgs;
import static edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts.fieldOwner;


/** Static exception/variable-seeded backward data-flow analysis. */
final class SeedBackwardStaticAnalyzer {
    private static final Logger LOG = LoggerFactory.getLogger(
            CausynthPipeline.class);
    private static final int MAX_ROUNDS = 96;
    private static final int DEFAULT_MAX_METHODS = 1000;
    private static final int DEFAULT_MAX_EDGES = 50000;
    private static final String MAX_METHODS_PROPERTY =
            "causynth.static.max.methods";
    private static final String MAX_EDGES_PROPERTY =
            "causynth.static.max.edges";
    private static final int MAX_RPC_TARGETS_PER_CALL = 6;
    private static final int MAX_DISPATCH_TARGETS_PER_CALL = 8;
    private static final int MAX_RUNTIME_RECURSIVE_METHODS = 128;
    private static final int MAX_CONSTRUCTOR_CALLERS_PER_PARAM = 80;
    private static final int MAX_METHOD_CALLERS_PER_METHOD = 200;
    private static final int MAX_FIELD_WRITERS_PER_FIELD = 80;
    private static final int MAX_FIELD_PATH_DEPTH = 4;
    private static final String HDFS_SASL_CLIENT =
            "org.apache.hadoop.hdfs.protocol.datatransfer.sasl.SaslDataTransferClient";
    private static final String HDFS_SASL_SERVER =
            "org.apache.hadoop.hdfs.protocol.datatransfer.sasl.SaslDataTransferServer";
    private static final String COMMON_SASL_SERVER =
            "org.apache.hadoop.security.SaslRpcServer";
    private static final String COMMON_SASL_CLIENT =
            "org.apache.hadoop.security.SaslRpcClient";
    private static final String COMMON_SECRET_MANAGER =
            "org.apache.hadoop.security.token.SecretManager";

    private final CausynthTargetContext target;
    private final int maxMethods;
    private final int maxEdges;
    private final Map<String, SootClass> classesByName = new LinkedHashMap<>();
    private final Map<String, SootMethod> methodsBySignature = new LinkedHashMap<>();
    private final Map<String, List<SootMethod>> concreteMethodsBySubSignature =
            new LinkedHashMap<>();
    private final Map<String, List<Fact>> factsByMethod = new LinkedHashMap<>();
    private final Map<String, List<Fact>> callersByCallee = new LinkedHashMap<>();
    private final Map<String, List<RpcTarget>> rpcTargetsBySource = new LinkedHashMap<>();
    private final Map<String, List<RpcTarget>> rpcSourcesByTarget = new LinkedHashMap<>();
    private final Map<String, List<FieldWrite>> fieldWritersByField =
            new LinkedHashMap<>();
    private final Map<String, List<ConstructorCallsite>> constructorCallersByCallee =
            new LinkedHashMap<>();
    private final Map<String, List<MethodCallsite>> methodCallersByCallee =
            new LinkedHashMap<>();
    private final Map<String, Set<String>> relevantFieldEffectsByMethod =
            new LinkedHashMap<>();
    private final List<StaticPortMapping> staticPortMappings = new ArrayList<>();
    private final Map<String, Set<String>> relevantByMethod = new LinkedHashMap<>();
    private final Set<String> selectedMethods = new LinkedHashSet<>();
    private final Map<String, Map<String, Object>> emittedEdgeRows =
            new LinkedHashMap<>();
    private final Set<String> emittedRpcMappings = new LinkedHashSet<>();
    private final Set<String> emittedStaticPortMappings = new LinkedHashSet<>();
    private final Set<String> expandedFieldWriterFields = new LinkedHashSet<>();
    private final Set<String> expandedConstructorCallees = new LinkedHashSet<>();
    private final Set<String> expandedMethodCallerKeys = new LinkedHashSet<>();
    private final Set<String> truncatedFieldWriterIndexFields =
            new LinkedHashSet<>();
    private final Set<String> truncatedMethodCallerIndexMethods =
            new LinkedHashSet<>();
    private final List<Map<String, Object>> discoveredExceptionSeeds = new ArrayList<>();
    private final Set<String> discoveredExceptionMethods = new LinkedHashSet<>();
    private final Set<String> discoveredExceptionVariables = new LinkedHashSet<>();
    private final Map<String, Boolean> receiverProjectionWriteSummary =
            new LinkedHashMap<>();
    private final Map<String, Set<String>> projectionAliasCache =
            new LinkedHashMap<>();
    private final Map<String, List<ExceptionGuard>> requiredPathGuardsByFact =
            new LinkedHashMap<>();
    private final Map<String, Boolean> exceptionReachabilityCache =
            new LinkedHashMap<>();
    private final RuntimeDispatchEvidence runtimeDispatchEvidence;
    private final Set<String> runtimeRecursiveMethods =
            new LinkedHashSet<>();
    private final Set<String> runtimeSelectedDispatchSites =
            new LinkedHashSet<>();
    private final Map<String, String> blockedRuntimeDispatchSites =
            new LinkedHashMap<>();
    private final List<Map<String, Object>> edges = new ArrayList<>();
    private boolean globalStaticIndexBuilt;
    private int globalStaticIndexCandidateMethodCount;
    private int globalStaticIndexIndexedMethodCount;
    private int globalStaticIndexUnreadableMethodCount;
    private int edgeCounter;
    private int projectedPassEdgeChecks;
    private int projectedPassUnsupported;
    private int projectedPassNoSuffix;
    private int projectedPassCandidates;
    private int projectedPassEmitted;

    SeedBackwardStaticAnalyzer(CausynthTargetContext target) {
        this.target = target;
        this.maxMethods = positiveSystemProperty(MAX_METHODS_PROPERTY,
                DEFAULT_MAX_METHODS);
        this.maxEdges = positiveSystemProperty(MAX_EDGES_PROPERTY,
                DEFAULT_MAX_EDGES);
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
        if (isHdfsKeyPropagationFastPathTarget()) {
            LOG.info("Using HDFS key-propagation scoped analysis");
            buildHdfsScopedRpcMappings();
            buildStaticPortMappings();
        } else {
            buildRpcMappings();
        }
        // Explicit project topology is orthogonal to the built-in RPC
        // discovery strategy.  In particular, a scoped HDFS analysis
        // must not silently ignore a configured cross-process boundary.
        buildConfiguredRpcPortMappings();
    }

    private static int positiveSystemProperty(String property,
                                              int defaultValue) {
        String configured;
        try {
            configured = System.getProperty(property);
        } catch (SecurityException ignored) {
            return defaultValue;
        }
        if (configured == null || configured.trim().isEmpty()) {
            return defaultValue;
        }
        try {
            int parsed = Integer.parseInt(configured.trim());
            return parsed > 0 ? parsed : defaultValue;
        } catch (NumberFormatException ignored) {
            return defaultValue;
        }
    }

    private void buildRpcMappings() {
        for (SootClass protocolClass : classesByName.values()) {
            if (!isRpcProtocolClass(protocolClass)) {
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
                    addRpcMapping(protocolMethod, concreteMethod,
                            "protocol_implementation");
                }
            }
        }
        LOG.info("Discovered {} static RPC method mappings",
                emittedRpcMappings.size());
    }

    /**
     * Loads project-owned RPC topology as navigation evidence only.  A
     * configured producer return and consumer RPC return become one
     * mapping-only static edge; RuntimeRegionPlanner must still observe
     * complete, equal endpoint fingerprints before promoting it to an
     * automatic EQUALITY relation.
     */
    private void buildConfiguredRpcPortMappings() {
        Path mappingFile = target.rpcMappingFile;
        if (mappingFile == null) return;
        ConfiguredRpcTopologyLoader.Result result =
                ConfiguredRpcTopologyLoader.load(mappingFile,
                        classesByName);
        for (ConfiguredRpcTopologyLoader.Mapping mapping
                : result.mappings()) {
            addStaticPortMapping("configured_rpc_return_mapping",
                    mapping.sourceMethod, mapping.sourceCell,
                    mapping.targetMethod, mapping.targetCell,
                    mapping.evidence);
        }
        LOG.info("Loaded {} configured mapping-only RPC return edges from {}",
                result.mappings().size(), mappingFile);
        if (result.downstreamDeclarationCount > 0) {
            LOG.info("Recognized {} downstream-only declared RPC "
                            + "equalities in {}; no static semantic edge "
                            + "was created",
                    result.downstreamDeclarationCount, mappingFile);
        }
    }

    private void buildStaticPortMappings() {
        buildHdfsDataTransferSaslPortMappings();
        buildHdfsServerSynchronousCallbackMappings();
        buildCommonSaslRpcPortMappings();
        buildHdfsHeartbeatKeyUpdatePortMappings();
        LOG.info("Discovered {} mapping-only static port candidates",
                staticPortMappings.size());
    }

    /**
     * Locates candidate endpoint ports in a configured workload.  This
     * mapping deliberately does not state that their values are equal or
     * that serialization is lossless; those facts require runtime value
     * evidence and captured region summaries.
     */
    private void buildHdfsHeartbeatKeyUpdatePortMappings() {
        SootMethod sender = findMethod(
                "org.apache.hadoop.hdfs.server.blockmanagement.BlockManager",
                "addKeyUpdateCommand", 2);
        if (sender == null) {
            return;
        }
        List<String> sources = invokeDefinitionCells(sender,
                "<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: "
                        + "org.apache.hadoop.hdfs.security.token.block.ExportedBlockKeys "
                        + "exportKeys()>");
        List<SootMethod> receivers = new ArrayList<>();
        addIfPresent(receivers, findMethod(
                "org.apache.hadoop.hdfs.server.datanode.BPOfferService",
                "processAccessKeyUpdateCommand", 3));
        // At the exact pre-HDFS-11741 revision the command handling is
        // still inlined in the active/standby switch methods.  Newer
        // revisions extracted processAccessKeyUpdateCommand.  Supporting
        // both shapes keeps the protocol model revision-independent.
        addIfPresent(receivers, findMethod(
                "org.apache.hadoop.hdfs.server.datanode.BPOfferService",
                "processCommandFromActive", 2));
        addIfPresent(receivers, findMethod(
                "org.apache.hadoop.hdfs.server.datanode.BPOfferService",
                "processCommandFromStandby", 2));
        for (SootMethod receiver : receivers) {
            List<String> targets = invokeDefinitionCells(receiver,
                    "<org.apache.hadoop.hdfs.server.protocol.KeyUpdateCommand: "
                            + "org.apache.hadoop.hdfs.security.token.block.ExportedBlockKeys "
                            + "getExportedKeys()>");
            for (String source : sources) {
                for (String targetCell : targets) {
                    addStaticPortMapping("hdfs_heartbeat_key_update",
                            sender.getSignature(), source,
                            receiver.getSignature(), targetCell,
                            "Mapping-only candidate between heartbeat endpoint ports; "
                                    + "no value relation is asserted");
                }
            }
        }
    }

    private void addIfPresent(List<SootMethod> methods, SootMethod method) {
        if (method != null) {
            methods.add(method);
        }
    }

    private void buildHdfsDataTransferSaslPortMappings() {
        SootMethod clientHandshake = findMethod(HDFS_SASL_CLIENT,
                "doSaslHandshake", 6);
        MethodSig clientSig = clientHandshake == null
                ? null
                : parseMethodSig(clientHandshake.getSignature());
        if (clientSig == null || clientSig.params.size() <= 3) {
            return;
        }
        String clientUserName = formalParam(clientSig, 3);

        for (MappedEndpoint endpoint : hdfsSaslServerUserNameEndpoints()) {
            addStaticPortMapping("hdfs_sasl_username",
                    clientHandshake.getSignature(), clientUserName,
                    endpoint.method, endpoint.cell,
                    "Mapping-only candidate between SASL endpoint ports; no value relation is asserted");
        }

        SootMethod serverHandshake = findMethod(HDFS_SASL_SERVER,
                "doSaslHandshake", 5);
        if (serverHandshake != null) {
            List<String> serverMagicValues = invokeDefinitionCells(
                    serverHandshake, "<java.io.DataInputStream: int readInt()>");
            String sentMagic = clientHandshake.getSignature()
                    + "#protocol:SASL_TRANSFER_MAGIC_NUMBER=-559038737";
            for (String serverMagic : serverMagicValues) {
                addStaticPortMapping("hdfs_sasl_magic_number",
                        clientHandshake.getSignature(), sentMagic,
                        serverHandshake.getSignature(), serverMagic,
                        "Mapping-only candidate between framed integer endpoint ports; no value relation is asserted");
            }
        }
    }

    /**
     * Connects the server-side callback registration to the callback body.
     *
     * <p>The callback is invoked from the JDK SASL implementation while
     * {@code doSaslHandshake} is still on the same thread.  It is therefore
     * an intraregion call, unlike the client-to-server SASL user-name
     * transfer above.  Both encrypted and general-purpose registrations are
     * discovered, but a binding is activated only after its concrete
     * {@code PasswordFunction.apply} implementation has independently
     * entered the exception-directed slice.  This gives the backward slice
     * a small object-sensitive dispatch rule: the HDFS-11741 path binds the
     * callback to {@code SaslDataTransferServer$1}, without also pulling in
     * the unrelated {@code $2} implementation.</p>
     */
    private void buildHdfsServerSynchronousCallbackMappings() {
        SootMethod handle = findMethod(
                HDFS_SASL_SERVER + "$SaslServerCallbackHandler",
                "handle", 1);
        SootMethod doHandshake = findMethod(HDFS_SASL_SERVER,
                "doSaslHandshake", 5);
        if (handle == null || doHandshake == null) {
            return;
        }

        String handleThis = thisCell(handle);
        String passwordFunctionReceiver = invokeReceiverCell(handle,
                HDFS_SASL_SERVER + "$PasswordFunction", "apply", 1);
        MethodSig handshakeSig = parseMethodSig(doHandshake.getSignature());
        Fact callbackInvocation = firstInvokeFact(doHandshake,
                "org.apache.hadoop.hdfs.protocol.datatransfer.sasl.SaslParticipant",
                "evaluateChallengeOrResponse", 1);
        if (handleThis.isEmpty() || passwordFunctionReceiver.isEmpty()
                || handshakeSig == null || callbackInvocation == null) {
            return;
        }
        String handshakeCallback = formalParam(handshakeSig, 4);

        for (String registrationName : Arrays.asList(
                "getEncryptedStreams", "getSaslStreams")) {
            SootMethod registration = findMethod(HDFS_SASL_SERVER,
                    registrationName, 3);
            CallbackRegistration binding = callbackRegistration(
                    registration);
            if (binding == null) {
                continue;
            }
            String evidence = "HDFS registers " + binding.implementationMethod
                    + " in SaslServerCallbackHandler and JDK SASL invokes handle "
                    + "synchronously on the registration thread";
            addStaticPortMapping("synchronous_callback_receiver",
                    registration.getSignature(), binding.handlerCell,
                    handle.getSignature(), handleThis, evidence,
                    binding.implementationMethod, doHandshake.getSignature(),
                    callbackInvocation, handshakeCallback);
            addStaticPortMapping("synchronous_callback_capture_receiver",
                    registration.getSignature(), binding.implementationCell,
                    handle.getSignature(), passwordFunctionReceiver, evidence,
                    binding.implementationMethod, doHandshake.getSignature(),
                    callbackInvocation, handshakeCallback);
        }
    }

    private CallbackRegistration callbackRegistration(SootMethod method) {
        if (method == null) {
            return null;
        }
        List<Fact> facts = factsFromMethod(method);
        String handlerConstructorOwner =
                HDFS_SASL_SERVER + "$SaslServerCallbackHandler";
        for (Fact fact : facts) {
            MethodSig invoked = parseMethodSig(fact.invoke);
            if (invoked == null || !"<init>".equals(invoked.name)
                    || !handlerConstructorOwner.equals(invoked.owner)) {
                continue;
            }
            List<String> rawActuals = actualInvokeArgs(fact.unitText);
            if (rawActuals.isEmpty()) {
                continue;
            }
            String implementationLocal = rawActuals.get(0);
            String implementationType = allocationTypeBefore(facts,
                    fact.unitIndex, implementationLocal);
            SootMethod implementation = findMethod(implementationType,
                    "apply", 1);
            String handlerLocal = invokeBaseLocal(fact.unitText);
            if (implementation == null || handlerLocal == null) {
                continue;
            }
            return new CallbackRegistration(
                    canonical(method.getSignature(), handlerLocal),
                    canonical(method.getSignature(), implementationLocal),
                    implementation.getSignature());
        }
        return null;
    }

    private String allocationTypeBefore(List<Fact> facts, int before,
                                        String local) {
        if (facts == null || local == null) {
            return "";
        }
        for (int index = Math.min(before - 1, facts.size() - 1);
             index >= 0; index--) {
            Unit unit = facts.get(index).unit;
            if (!(unit instanceof AssignStmt)) {
                continue;
            }
            AssignStmt assignment = (AssignStmt) unit;
            if (!local.equals(assignment.getLeftOp().toString())) {
                continue;
            }
            Matcher allocation = Pattern.compile("^new\\s+([^\\s]+)$")
                    .matcher(assignment.getRightOp().toString().trim());
            return allocation.matches() ? allocation.group(1) : "";
        }
        return "";
    }

    private String thisCell(SootMethod method) {
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return "";
        }
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof IdentityStmt)) {
                continue;
            }
            IdentityStmt identity = (IdentityStmt) unit;
            if (identity.getRightOp().toString().startsWith("@this:")) {
                return canonical(method.getSignature(),
                        identity.getLeftOp().toString());
            }
        }
        return "";
    }

    private String invokeReceiverCell(SootMethod method, String owner,
                                      String name, int paramCount) {
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return "";
        }
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            MethodSig signature = parseMethodSig(
                    invoke.getMethodRef().getSignature());
            if (signature == null || !owner.equals(signature.owner)
                    || !name.equals(signature.name)
                    || signature.params.size() != paramCount
                    || !(invoke instanceof InstanceInvokeExpr)) {
                continue;
            }
            return canonical(method.getSignature(),
                    ((InstanceInvokeExpr) invoke).getBase().toString());
        }
        return "";
    }

    private Fact firstInvokeFact(SootMethod method, String owner,
                                 String name, int paramCount) {
        for (Fact fact : factsFromMethod(method)) {
            MethodSig invoked = parseMethodSig(fact.invoke);
            if (invoked != null && owner.equals(invoked.owner)
                    && name.equals(invoked.name)
                    && invoked.params.size() == paramCount) {
                return fact;
            }
        }
        return null;
    }

    private void buildCommonSaslRpcPortMappings() {
        SootMethod clientHandle = findMethod(
                COMMON_SASL_CLIENT + "$SaslClientCallbackHandler",
                "handle", 1);
        SootMethod serverHandle = findMethod(
                COMMON_SASL_SERVER + "$SaslDigestCallbackHandler",
                "handle", 1);
        if (clientHandle == null || serverHandle == null) {
            return;
        }
        List<String> sources = invokeArgumentCells(clientHandle,
                "<javax.security.auth.callback.NameCallback: void setName(java.lang.String)>",
                0);
        List<String> targets = invokeDefinitionCells(serverHandle,
                "<javax.security.auth.callback.NameCallback: java.lang.String getDefaultName()>");
        for (String source : sources) {
            for (String targetCell : targets) {
                addStaticPortMapping("common_sasl_rpc_username",
                        clientHandle.getSignature(), source,
                        serverHandle.getSignature(), targetCell,
                        "Mapping-only candidate between callback endpoint ports; "
                                + "no value relation is asserted");
            }
        }

        SootMethod getIdentifier = findMethod(COMMON_SASL_SERVER,
                "getIdentifier", 2);
        MethodSig getIdentifierSig = getIdentifier == null
                ? null : parseMethodSig(getIdentifier.getSignature());
        if (getIdentifierSig != null) {
            addStaticPortMapping("identifier_deserialization_return",
                    getIdentifier.getSignature(),
                    formalParam(getIdentifierSig, 0),
                    getIdentifier.getSignature(),
                    getIdentifier.getSignature() + ".return",
                    "Mapping-only candidate between decoder input/output ports; "
                            + "the transformer must come from a region summary");
        }
    }

    private List<String> invokeArgumentCells(SootMethod method,
                                             String invokeSignature,
                                             int argumentIndex) {
        List<String> cells = new ArrayList<>();
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException exception) {
            return cells;
        }
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            if (!invokeSignature.equals(invoke.getMethodRef().getSignature())
                    || argumentIndex < 0 || argumentIndex >= invoke.getArgCount()) {
                continue;
            }
            String cell = canonical(method.getSignature(),
                    invoke.getArg(argumentIndex).toString());
            if (!ignoreNode(cell)) {
                cells.add(cell);
            }
        }
        return cells;
    }

    private List<String> invokeDefinitionCells(SootMethod method,
                                               String invokeSignature) {
        List<String> cells = new ArrayList<>();
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException exception) {
            return cells;
        }
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()
                    || !invokeSignature.equals(((Stmt) unit).getInvokeExpr()
                    .getMethodRef().getSignature())) {
                continue;
            }
            for (ValueBox box : unit.getDefBoxes()) {
                String cell = canonical(method.getSignature(),
                        box.getValue().toString());
                if (!ignoreNode(cell)) {
                    cells.add(cell);
                }
            }
        }
        return cells;
    }

    private List<MappedEndpoint> hdfsSaslServerUserNameEndpoints() {
        List<MappedEndpoint> endpoints = new ArrayList<>();
        SootMethod handle = findMethod(HDFS_SASL_SERVER + "$SaslServerCallbackHandler",
                "handle", 1);
        if (handle == null) {
            return endpoints;
        }
        Body body;
        try {
            body = handle.retrieveActiveBody();
        } catch (RuntimeException exception) {
            return endpoints;
        }
        for (Unit unit : body.getUnits()) {
            if (!nameCallbackDefaultNameInvoke(unit)) {
                continue;
            }
            for (ValueBox box : unit.getDefBoxes()) {
                String cell = canonical(handle.getSignature(),
                        box.getValue().toString());
                if (!ignoreNode(cell)) {
                    endpoints.add(new MappedEndpoint(handle.getSignature(), cell));
                }
            }
        }
        return endpoints;
    }

    private boolean nameCallbackDefaultNameInvoke(Unit unit) {
        if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) {
            return false;
        }
        String signature = ((Stmt) unit).getInvokeExpr().getMethodRef()
                .getSignature();
        return "<javax.security.auth.callback.NameCallback: java.lang.String getDefaultName()>"
                .equals(signature);
    }

    private SootMethod findMethod(String owner, String name, int paramCount) {
        SootClass sootClass = classesByName.get(owner);
        if (sootClass == null) {
            return null;
        }
        for (SootMethod method : sootClass.getMethods()) {
            MethodSig sig = parseMethodSig(method.getSignature());
            if (sig != null
                    && method.isConcrete()
                    && name.equals(sig.name)
                    && sig.params.size() == paramCount) {
                return method;
            }
        }
        return null;
    }

    private void addStaticPortMapping(String kind, String sourceMethod,
                                      String sourceCell, String targetMethod,
                                      String targetCell, String evidence) {
        addStaticPortMapping(kind, sourceMethod, sourceCell, targetMethod,
                targetCell, evidence, "", targetMethod, null, "");
    }

    private void addStaticPortMapping(String kind, String sourceMethod,
                                      String sourceCell, String targetMethod,
                                      String targetCell, String evidence,
                                      String activationMethod,
                                      String edgeMethod, Fact pathSite,
                                      String pathCell) {
        String key = kind + "\n" + sourceCell + "\n" + targetCell;
        if (!emittedStaticPortMappings.add(key)) {
            return;
        }
        staticPortMappings.add(new StaticPortMapping(kind, sourceMethod,
                sourceCell, targetMethod, targetCell, evidence,
                activationMethod, edgeMethod, pathSite, pathCell));
    }

    private boolean isRpcProtocolClass(SootClass sootClass) {
        String name = sootClass.getName();
        return sootClass.isInterface()
                && (name.contains("Protocol")
                || name.contains("protocolPB")
                || name.endsWith("PB"));
    }

    private void addRpcMapping(SootMethod source, SootMethod targetMethod,
                               String kind) {
        RpcTarget target = new RpcTarget(source.getSignature(),
                targetMethod.getSignature(), kind);
        String key = target.sourceSignature + "\n" + target.targetSignature;
        if (!emittedRpcMappings.add(key)) {
            return;
        }
        rpcTargetsBySource.computeIfAbsent(target.sourceSignature,
                ignored -> new ArrayList<>()).add(target);
        rpcSourcesByTarget.computeIfAbsent(target.targetSignature,
                ignored -> new ArrayList<>()).add(target);
    }

    private void buildHdfsScopedRpcMappings() {
        addHdfsRpcMapping(
                "org.apache.hadoop.hdfs.server.protocol.NamenodeProtocol",
                "getBlockKeys", 0,
                "org.apache.hadoop.hdfs.protocolPB.NamenodeProtocolTranslatorPB",
                "getBlockKeys", 0);
        addHdfsRpcMapping(
                "org.apache.hadoop.hdfs.server.protocol.NamenodeProtocol",
                "getBlockKeys", 0,
                "org.apache.hadoop.hdfs.server.namenode.NameNodeRpcServer",
                "getBlockKeys", 0);
        addRpcMappingBySignature(
                "<org.apache.hadoop.hdfs.protocolPB.NamenodeProtocolPB: "
                        + "org.apache.hadoop.hdfs.protocol.proto.NamenodeProtocolProtos$GetBlockKeysResponseProto "
                        + "getBlockKeys(com.google.protobuf.RpcController,"
                        + "org.apache.hadoop.hdfs.protocol.proto.NamenodeProtocolProtos$GetBlockKeysRequestProto)>",
                "<org.apache.hadoop.hdfs.protocolPB.NamenodeProtocolServerSideTranslatorPB: "
                        + "org.apache.hadoop.hdfs.protocol.proto.NamenodeProtocolProtos$GetBlockKeysResponseProto "
                        + "getBlockKeys(com.google.protobuf.RpcController,"
                        + "org.apache.hadoop.hdfs.protocol.proto.NamenodeProtocolProtos$GetBlockKeysRequestProto)>",
                "hdfs_scoped_pb_rpc");
        LOG.info("Discovered {} HDFS-scoped RPC method mappings",
                emittedRpcMappings.size());
    }

    private void addRpcMappingBySignature(String sourceSignature,
                                          String targetSignature,
                                          String kind) {
        RpcTarget target = new RpcTarget(sourceSignature, targetSignature, kind);
        String key = target.sourceSignature + "\n" + target.targetSignature;
        if (!emittedRpcMappings.add(key)) {
            return;
        }
        rpcTargetsBySource.computeIfAbsent(target.sourceSignature,
                ignored -> new ArrayList<>()).add(target);
        rpcSourcesByTarget.computeIfAbsent(target.targetSignature,
                ignored -> new ArrayList<>()).add(target);
    }

    private void addHdfsRpcMapping(String sourceOwner, String sourceName,
                                   int sourceParamCount,
                                   String targetOwner, String targetName,
                                   int targetParamCount) {
        SootMethod source = findAnyMethod(sourceOwner, sourceName, sourceParamCount);
        SootMethod targetMethod = findAnyMethod(targetOwner, targetName,
                targetParamCount);
        if (source == null || targetMethod == null) {
            return;
        }
        addRpcMapping(source, targetMethod, "hdfs_scoped_rpc");
    }

    private SootMethod findAnyMethod(String owner, String name, int paramCount) {
        SootClass sootClass = classesByName.get(owner);
        if (sootClass == null) {
            return null;
        }
        for (SootMethod method : sootClass.getMethods()) {
            MethodSig sig = parseMethodSig(method.getSignature());
            if (sig != null
                    && name.equals(sig.name)
                    && sig.params.size() == paramCount) {
                return method;
            }
        }
        return null;
    }

    private boolean classImplementsOrExtends(SootClass candidate, String targetClassName) {
        return classImplementsOrExtends(candidate, targetClassName, new LinkedHashSet<>());
    }

    private boolean classImplementsOrExtends(SootClass candidate, String targetClassName,
                                             Set<String> seen) {
        if (candidate == null || !seen.add(candidate.getName())) {
            return false;
        }
        if (candidate.getName().equals(targetClassName)) {
            return true;
        }
        try {
            for (SootClass iface : candidate.getInterfaces()) {
                if (classImplementsOrExtends(iface, targetClassName, seen)) {
                    return true;
                }
            }
            if (candidate.hasSuperclass()) {
                return classImplementsOrExtends(candidate.getSuperclass(),
                        targetClassName, seen);
            }
        } catch (RuntimeException ignored) {
            return false;
        }
        return false;
    }

    CausynthAnalysisResult analyze() throws IOException {
        CausynthAnalysisResult result = new CausynthAnalysisResult();
        result.targetResolved.put("seedMode", target.seedMode());
        result.targetResolved.put("seedException", target.seedException);
        result.targetResolved.put("seedVariables", target.seedVariables);
        result.targetResolved.put("seedFunction", target.seedFunction);
        result.targetResolved.put("seedPredicate", target.seedPredicate());
        result.targetResolved.put("seedMap", target.seedMapName());
        result.targetResolved.put("seedKeyExpression", target.seedKeyExpression());
        result.targetResolved.put("analysisScope", target.analysisScope);
        result.targetResolved.put("repoRoot", target.repoRoot.toString());
        result.targetResolved.put("moduleDir", target.moduleDir.toString());

        if (target.exceptionSeeded()) {
            result.seeds.add(object(
                    "id", "seed.exception_target",
                    "kind", "exception_target",
                    "exception", target.seedException,
                    "discovery", "STATIC_THROW_GUARD_AND_PAYLOAD"));
        } else {
            result.seeds.add(object(
                    "id", "seed.local_condition",
                    "kind", "local_condition",
                    "predicate", target.seedPredicate(),
                    "variables", target.seedVariables));
        }

        if (isHdfsKeyPropagationFastPathTarget()) {
            Set<String> candidateClasses = hdfsPropagationClasses();
            loadScopedHdfsPropagationMethods(candidateClasses);
            // Seed the exact scalar component used to build the encrypted
            // SASL user name before the exception worklist opens broad
            // shared-field writer frontiers.  This is a data-dependency
            // seed, not a value-equality assertion: the enclosing method
            // still has to be captured as a normal symbolic region to
            // learn the integer-to-string encoding.
            initializeHdfsSaslUsernameKeyIdProducer();
            initializeConfiguredSeedAnchors();
            runWorklist();
            finishSeedDiscovery(result);

            result.edges.addAll(edges);
            result.cells.addAll(collectCells());
            result.traceMethods.addAll(collectLoadedTraceMethods());
            result.slices.put("strategy",
                    "HDFS-scoped seed backward static analysis over the NameNode/Balancer/DataNode block-key propagation chain");
            result.slices.put("candidateClassCount", candidateClasses.size());
            result.slices.put("rpcMappingCount", emittedRpcMappings.size());
            result.slices.put("staticPortMappingCount", staticPortMappings.size());
            result.slices.put("fieldWriterIndexedFieldCount",
                    fieldWritersByField.size());
            result.slices.put("fieldWriterExpandedFieldCount",
                    expandedFieldWriterFields.size());
            result.slices.put("constructorCallerIndexedConstructorCount",
                    constructorCallersByCallee.size());
            result.slices.put("constructorCallerExpandedConstructorCount",
                    expandedConstructorCallees.size());
            result.slices.put("methodCallerIndexedMethodCount",
                    methodCallersByCallee.size());
            result.slices.put("methodCallerExpandedKeyCount",
                    expandedMethodCallerKeys.size());
            addGlobalStaticIndexSummary(result.slices);
            addRuntimeDispatchSummary(result.slices);
            result.slices.put("loadedMethodCount", factsByMethod.size());
            result.slices.put("selectedMethodCount", selectedMethods.size());
            result.slices.put("edgeCount", edges.size());
            result.slices.put("edgeKinds", summarizeEdgeKinds(edges));
            result.slices.put("projectedPassEdgeChecks", projectedPassEdgeChecks);
            result.slices.put("projectedPassUnsupported", projectedPassUnsupported);
            result.slices.put("projectedPassNoSuffix", projectedPassNoSuffix);
            result.slices.put("projectedPassCandidates", projectedPassCandidates);
            result.slices.put("projectedPassEmitted", projectedPassEmitted);
            addStaticAnalysisBudgetSummary(result);
            return result;
        }

        Set<String> candidateClasses = findCandidateClasses();
        loadClasses(candidateClasses);
        loadStaticPortMappingClasses();
        initializeConfiguredSeedAnchors();
        runWorklist();
        finishSeedDiscovery(result);

        result.edges.addAll(edges);
        result.cells.addAll(collectCells());
        result.traceMethods.addAll(collectTraceMethods());
        result.slices.put("strategy",
                "seed-only backward static analysis over Jimple def-use, calls, field writers, RPC mappings, and hard-coded SASL handshake dataflow");
        result.slices.put("candidateClassCount", candidateClasses.size());
        result.slices.put("rpcMappingCount", emittedRpcMappings.size());
        result.slices.put("staticPortMappingCount", staticPortMappings.size());
        result.slices.put("fieldWriterIndexedFieldCount",
                fieldWritersByField.size());
        result.slices.put("fieldWriterExpandedFieldCount",
                expandedFieldWriterFields.size());
        result.slices.put("constructorCallerIndexedConstructorCount",
                constructorCallersByCallee.size());
        result.slices.put("constructorCallerExpandedConstructorCount",
                expandedConstructorCallees.size());
        result.slices.put("methodCallerIndexedMethodCount",
                methodCallersByCallee.size());
        result.slices.put("methodCallerExpandedKeyCount",
                expandedMethodCallerKeys.size());
        addGlobalStaticIndexSummary(result.slices);
        addRuntimeDispatchSummary(result.slices);
        result.slices.put("loadedMethodCount", factsByMethod.size());
        result.slices.put("selectedMethodCount", selectedMethods.size());
        result.slices.put("edgeCount", edges.size());
        result.slices.put("edgeKinds", summarizeEdgeKinds(edges));
        result.slices.put("projectedPassEdgeChecks", projectedPassEdgeChecks);
        result.slices.put("projectedPassUnsupported", projectedPassUnsupported);
        result.slices.put("projectedPassNoSuffix", projectedPassNoSuffix);
        result.slices.put("projectedPassCandidates", projectedPassCandidates);
        result.slices.put("projectedPassEmitted", projectedPassEmitted);
        addStaticAnalysisBudgetSummary(result);
        return result;
    }

    private void addStaticAnalysisBudgetSummary(
            CausynthAnalysisResult result) {
        boolean methodCapReached = selectedMethods.size() >= maxMethods;
        boolean edgeCapReached = edges.size() >= maxEdges;
        Map<String, Object> budget = object(
                "authority",
                "JVM_SYSTEM_PROPERTY_WITH_POSITIVE_DEFAULT_V1",
                "maxMethodsProperty", MAX_METHODS_PROPERTY,
                "maxEdgesProperty", MAX_EDGES_PROPERTY,
                "maxMethods", maxMethods,
                "maxEdges", maxEdges,
                "selectedMethodCount", selectedMethods.size(),
                "emittedEdgeCount", edges.size(),
                "methodCapReached", methodCapReached,
                "edgeCapReached", edgeCapReached,
                "capReached", methodCapReached || edgeCapReached,
                "complete", !methodCapReached && !edgeCapReached);
        result.slices.put("staticAnalysisBudget", budget);
        result.symbolicCoverage.put("staticAnalysisBudget",
                new LinkedHashMap<>(budget));
    }

    private void addGlobalStaticIndexSummary(Map<String, Object> slices) {
        slices.put("globalStaticIndexScope",
                "ALL_APPLICATION_CONCRETE_METHODS");
        slices.put("globalStaticIndexCandidateMethodCount",
                globalStaticIndexCandidateMethodCount);
        slices.put("globalStaticIndexIndexedMethodCount",
                globalStaticIndexIndexedMethodCount);
        slices.put("globalStaticIndexUnreadableMethodCount",
                globalStaticIndexUnreadableMethodCount);
        slices.put("fieldWriterIndexTruncatedFieldCount",
                truncatedFieldWriterIndexFields.size());
        slices.put("methodCallerIndexTruncatedMethodCount",
                truncatedMethodCallerIndexMethods.size());
        slices.put("globalStaticIndexComplete", globalStaticIndexBuilt
                && globalStaticIndexUnreadableMethodCount == 0
                && truncatedFieldWriterIndexFields.isEmpty()
                && truncatedMethodCallerIndexMethods.isEmpty());
        slices.put("globalStaticIndexAuthority",
                "ALL_APPLICATION_METHOD_SCAN_WITH_EXPLICIT_INCOMPLETE_ON_BOUND_OR_BODY_FAILURE_V1");
    }

    private void addRuntimeDispatchSummary(Map<String, Object> slices) {
        slices.put("runtimeDispatchEvidenceConfigured",
                runtimeDispatchEvidence.configured());
        slices.put("runtimeDispatchEvidenceSource",
                runtimeDispatchEvidence.source());
        slices.put("runtimeDispatchEvidenceRowCount",
                runtimeDispatchEvidence.rowCount());
        slices.put("runtimeDispatchEvidenceSiteCount",
                runtimeDispatchEvidence.siteCount());
        slices.put("runtimeDispatchEvidenceRejectedRowCount",
                runtimeDispatchEvidence.rejectedRowCount());
        slices.put("runtimeSelectedDispatchSiteCount",
                runtimeSelectedDispatchSites.size());
        slices.put("runtimeSelectedDispatchSites",
                sortedLimited(runtimeSelectedDispatchSites,
                        Integer.MAX_VALUE));
        slices.put("runtimeRecursiveMethodCount",
                runtimeRecursiveMethods.size());
        slices.put("runtimeRecursiveMethods",
                sortedLimited(runtimeRecursiveMethods,
                        Integer.MAX_VALUE));
        slices.put("blockedRuntimeDispatchSites",
                new LinkedHashMap<>(blockedRuntimeDispatchSites));
        slices.put("runtimeDispatchSelectionComplete",
                runtimeDispatchEvidence.rejectedRowCount() == 0
                        && blockedRuntimeDispatchSites.isEmpty());
        slices.put("runtimeDispatchSelectionAuthority",
                runtimeDispatchEvidence.configured()
                        ? "UNIQUE_CALLSITE_CORRELATED_ACTUAL_CALLEE_V1"
                        : "STATIC_CLASS_HIERARCHY_FALLBACK");
    }

    private void initializeConfiguredSeedAnchors() {
        if (target.exceptionSeeded()) {
            initializeExceptionSeedAnchors();
            return;
        }
        initializeSeedAnchors();
        initializeHdfsDirectLookupSeedAnchors();
    }

    /**
     * Adds the exact leaf dependency that Jimple's mutable StringBuilder
     * lowering otherwise discovers only after walking every append state.
     *
     * <p>The edge says only that {@code DataEncryptionKey.keyId}
     * contributes to the returned username.  It intentionally does not
     * claim equality: concolic execution of the ordinary method region is
     * responsible for its decimal-string/compound-username semantics.
     * The source is the scalar leaf owned by parameter zero, never the
     * {@code DataEncryptionKey} object reference.</p>
     */
    private void initializeHdfsSaslUsernameKeyIdProducer() {
        SootMethod method = findMethod(HDFS_SASL_CLIENT,
                "getUserNameFromEncryptionKey", 1);
        MethodSig signature = method == null ? null
                : parseMethodSig(method.getSignature());
        if (signature == null
                || signature.params.size() != 1
                || !"org.apache.hadoop.hdfs.security.token.block."
                .concat("DataEncryptionKey").equals(
                erasedTypeName(signature.params.get(0)))
                || !"java.lang.String".equals(signature.returnType)) {
            return;
        }
        SootField keyId = resolveDeclaredField(signature.params.get(0),
                "keyId");
        if (keyId == null || !"int".equals(keyId.getType().toString())) {
            return;
        }
        List<Fact> facts = factsByMethod.get(method.getSignature());
        if (facts == null) {
            facts = factsFromMethod(method);
        }
        if (!hdfsUsernameMethodEncodesKeyId(method.getSignature(), facts,
                keyId.getSignature())) {
            return;
        }

        String source = formalParam(signature, 0) + "#field:keyId";
        String output = method.getSignature() + ".return";
        addEdge("structured_scalar_encoding_dependency", source, output,
                method.getSignature(), null,
                "HDFS encrypted SASL username decimal-encodes DataEncryptionKey.keyId as its first component");
        Map<String, Object> edge = emittedEdgeRows.get(edgeKey(
                "structured_scalar_encoding_dependency", source, output,
                method.getSignature()));
        if (edge != null) {
            edge.put("sourceFieldSignature", keyId.getSignature());
            edge.put("structuredEncoding", "DECIMAL_KEY_ID_PREFIX");
            edge.put("componentDelimiter", " ");
            edge.put("dependencyAuthority",
                    "SOOT_HDFS_USERNAME_KEYID_FIELD_READ_V1");
            edge.put("valueEqualityAsserted", false);
            edge.put("objectReferenceIsSymbolicScalar", false);
        }
        relevant(method.getSignature()).add(source);
        relevant(method.getSignature()).add(output);
        selectedMethods.add(method.getSignature());
    }

    private boolean hdfsUsernameMethodEncodesKeyId(
            String method, List<Fact> facts, String keyIdField) {
        if (facts == null || facts.isEmpty()) {
            return false;
        }
        Set<String> parameterAliases = new LinkedHashSet<>();
        boolean returnsString = false;
        for (Fact fact : facts) {
            if (fact.unit instanceof IdentityStmt) {
                IdentityStmt identity = (IdentityStmt) fact.unit;
                if (identity.getRightOp() instanceof ParameterRef
                        && ((ParameterRef) identity.getRightOp()).getIndex()
                        == 0) {
                    parameterAliases.add(canonical(method,
                            identity.getLeftOp().toString()));
                }
            }
            returnsString |= fact.isReturn;
        }
        parameterAliases = closeLocalAliases(method, facts,
                parameterAliases);

        boolean readsKeyId = false;
        for (Fact fact : facts) {
            for (InstanceFieldAccess access : fact.instanceFieldUses) {
                if (keyIdField.equals(access.field)
                        && parameterAliases.contains(canonical(method,
                        access.base))) {
                    readsKeyId = true;
                }
            }
        }
        // The method/parameter/field tuple is HDFS-specific and the edge
        // asserts dependency only (never equality).  A direct Soot field
        // read plus a returned String is therefore sufficient authority;
        // the concolic region records the concrete StringBuilder encoding.
        return returnsString && readsKeyId;
    }

    private void finishSeedDiscovery(CausynthAnalysisResult result) {
        result.seeds.addAll(discoveredExceptionSeeds);
        result.targetResolved.put("discoveredSeedCount",
                discoveredExceptionSeeds.size());
        result.targetResolved.put("discoveredSeedMethods",
                new ArrayList<>(discoveredExceptionMethods));
        result.targetResolved.put("discoveredSeedVariables",
                new ArrayList<>(discoveredExceptionVariables));
        if (target.exceptionSeeded() && discoveredExceptionSeeds.isEmpty()) {
            throw new IllegalStateException("No direct throw site found for seed exception "
                    + target.seedException + " in the loaded analysis scope");
        }
    }

    private List<Map<String, Object>> collectTraceMethods() {
        List<String> methods = new ArrayList<>(selectedMethods);
        Collections.sort(methods);
        List<Map<String, Object>> rows = new ArrayList<>();
        int index = 0;
        for (String method : methods) {
            rows.add(object("id", "TM." + index++, "method", method));
        }
        return rows;
    }

    private List<Map<String, Object>> collectLoadedTraceMethods() {
        List<String> methods = new ArrayList<>(factsByMethod.keySet());
        Collections.sort(methods);
        List<Map<String, Object>> rows = new ArrayList<>();
        int index = 0;
        for (String method : methods) {
            rows.add(object("id", "TM." + index++, "method", method));
        }
        return rows;
    }

    private boolean isHdfsKeyPropagationFastPathTarget() {
        String scope = target.analysisScope == null
                ? ""
                : target.analysisScope.trim().toLowerCase(Locale.ROOT);
        return "hdfs_block_key".equals(scope)
                || "hdfs-key-propagation".equals(scope)
                || "hdfs_key_propagation".equals(scope);
    }

    private Set<String> hdfsPropagationClasses() {
        return new LinkedHashSet<>(Arrays.asList(
                "org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager",
                "org.apache.hadoop.hdfs.security.token.block.BlockPoolTokenSecretManager",
                "org.apache.hadoop.hdfs.security.token.block.ExportedBlockKeys",
                "org.apache.hadoop.hdfs.security.token.block.BlockKey",
                "org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey",
                "org.apache.hadoop.hdfs.server.balancer.KeyManager",
                "org.apache.hadoop.hdfs.server.balancer.KeyManager$BlockKeyUpdater",
                "org.apache.hadoop.hdfs.server.balancer.Dispatcher",
                "org.apache.hadoop.hdfs.protocolPB.NamenodeProtocolTranslatorPB",
                "org.apache.hadoop.hdfs.protocolPB.NamenodeProtocolPB",
                "org.apache.hadoop.hdfs.protocolPB.NamenodeProtocolServerSideTranslatorPB",
                "org.apache.hadoop.hdfs.protocolPB.PBHelper",
                "org.apache.hadoop.hdfs.server.protocol.NamenodeProtocol",
                "org.apache.hadoop.hdfs.server.namenode.NameNodeRpcServer",
                "org.apache.hadoop.hdfs.server.namenode.FSNamesystem",
                "org.apache.hadoop.hdfs.server.blockmanagement.BlockManager",
                "org.apache.hadoop.hdfs.server.datanode.BPOfferService",
                "org.apache.hadoop.hdfs.server.protocol.KeyUpdateCommand",
                "org.apache.hadoop.hdfs.server.protocol.DatanodeRegistration",
                "org.apache.hadoop.hdfs.protocol.datatransfer.sasl.DataEncryptionKeyFactory",
                HDFS_SASL_CLIENT,
                HDFS_SASL_CLIENT + "$SaslClientCallbackHandler",
                HDFS_SASL_SERVER,
                HDFS_SASL_SERVER + "$SaslServerCallbackHandler",
                COMMON_SASL_SERVER,
                COMMON_SASL_SERVER + "$SaslDigestCallbackHandler",
                COMMON_SASL_CLIENT,
                COMMON_SASL_CLIENT + "$SaslClientCallbackHandler",
                COMMON_SECRET_MANAGER));
    }

    private void loadScopedHdfsPropagationMethods(Set<String> classNames) {
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            String className = sootClass.getName();
            if (!hdfsPropagationClassAllowed(classNames, className)) {
                continue;
            }
            for (SootMethod method : sootClass.getMethods()) {
                if (hdfsPropagationMethodAllowed(method)) {
                    loadMethod(method);
                }
            }
        }
        LOG.info("Loaded {} HDFS-scoped propagation methods from {} classes",
                factsByMethod.size(), classNames.size());
    }

    private boolean hdfsPropagationClassAllowed(Set<String> classNames,
                                                String className) {
        if (classNames.contains(className)) {
            return true;
        }
        return className.startsWith(HDFS_SASL_SERVER + "$")
                || className.startsWith(HDFS_SASL_CLIENT + "$")
                || className.startsWith(COMMON_SASL_SERVER + "$")
                || className.startsWith(COMMON_SASL_CLIENT + "$")
                || className.startsWith(
                "org.apache.hadoop.hdfs.server.balancer.Dispatcher$");
    }

    private boolean hdfsPropagationMethodAllowed(SootMethod method) {
        if (method == null || !method.isConcrete()) {
            return false;
        }
        MethodSig sig = parseMethodSig(method.getSignature());
        if (sig == null) {
            return false;
        }
        String owner = sig.owner;
        String name = sig.name;
        if ("<clinit>".equals(name)) {
            return false;
        }
        if ("<init>".equals(name)) {
            return owner.contains("KeyManager")
                    || owner.endsWith("BlockTokenSecretManager")
                    || owner.endsWith("BlockPoolTokenSecretManager")
                    || owner.endsWith("ExportedBlockKeys")
                    || owner.endsWith("BlockKey")
                    || owner.endsWith("DataEncryptionKey")
                    || owner.endsWith("KeyUpdateCommand")
                    || owner.endsWith("DatanodeRegistration")
                    || owner.contains("SaslDataTransfer")
                    || owner.startsWith(COMMON_SASL_SERVER + "$")
                    || owner.startsWith(COMMON_SASL_CLIENT + "$");
        }
        if (owner.equals(COMMON_SECRET_MANAGER)) {
            return "retriableRetrievePassword".equals(name);
        }
        if (owner.equals(COMMON_SASL_SERVER)) {
            return Arrays.asList("getIdentifier", "decodeIdentifier",
                    "encodeIdentifier", "encodePassword").contains(name);
        }
        if (owner.equals(COMMON_SASL_SERVER + "$SaslDigestCallbackHandler")) {
            return "handle".equals(name) || "getPassword".equals(name);
        }
        if (owner.equals(COMMON_SASL_CLIENT + "$SaslClientCallbackHandler")) {
            return "handle".equals(name);
        }
        if (owner.startsWith("org.apache.hadoop.hdfs.server.balancer.Dispatcher$")) {
            return "dispatch".equals(name);
        }
        if (owner.endsWith("BlockTokenSecretManager")) {
            return Arrays.asList("exportKeys", "addKeys", "removeExpiredKeys",
                    "updateKeys", "generateKeys", "generateDataEncryptionKey",
                    "generateDataEncryptionKeyForTesting", "retrievePassword",
                    "retrieveDataEncryptionKey", "getNonceGenerator", "hasKey")
                    .contains(name);
        }
        if (owner.endsWith("BlockPoolTokenSecretManager")) {
            return Arrays.asList("get", "addKeys", "retrievePassword",
                    "retrieveDataEncryptionKey").contains(name);
        }
        if (owner.endsWith("ExportedBlockKeys") || owner.endsWith("BlockKey")
                || owner.endsWith("DataEncryptionKey")) {
            return name.startsWith("get") || name.startsWith("is");
        }
        if (owner.equals("org.apache.hadoop.hdfs.server.balancer.KeyManager")) {
            return Arrays.asList("startBlockKeyUpdater", "getAccessToken",
                    "newDataEncryptionKey", "newDataEncryptionKeyForTesting",
                    "close").contains(name);
        }
        if (owner.equals("org.apache.hadoop.hdfs.server.balancer.KeyManager$BlockKeyUpdater")) {
            return "run".equals(name) || "close".equals(name);
        }
        if (owner.equals("org.apache.hadoop.hdfs.server.balancer.Dispatcher")) {
            if (name.startsWith("access$")) {
                return true;
            }
            return name.contains("EncryptedSasl")
                    || name.contains("Missing")
                    || "containsGhostKey".equals(name);
        }
        if (owner.equals("org.apache.hadoop.hdfs.protocolPB.NamenodeProtocolTranslatorPB")
                || owner.equals("org.apache.hadoop.hdfs.protocolPB.NamenodeProtocolServerSideTranslatorPB")
                || owner.equals("org.apache.hadoop.hdfs.server.namenode.NameNodeRpcServer")) {
            return "getBlockKeys".equals(name);
        }
        if (owner.equals("org.apache.hadoop.hdfs.protocolPB.PBHelper")) {
            return "convert".equals(name)
                    && (method.getSignature().contains("ExportedBlockKeys")
                    || method.getSignature().contains("BlockKey"));
        }
        if (owner.equals("org.apache.hadoop.hdfs.server.namenode.FSNamesystem")) {
            return "getBlockManager".equals(name);
        }
        if (owner.equals("org.apache.hadoop.hdfs.server.blockmanagement.BlockManager")) {
            return Arrays.asList("getBlockKeys", "addKeyUpdateCommand",
                    "shouldUpdateBlockKey", "generateDataEncryptionKey")
                    .contains(name);
        }
        if (owner.equals("org.apache.hadoop.hdfs.server.datanode.BPOfferService")) {
            return Arrays.asList("processHeartbeatResponseForTesting",
                    "processAccessKeyUpdateCommand", "registrationSucceeded",
                    "processCommandFromActor", "processCommandFromActive",
                    "processCommandFromStandby", "getBlockPoolId").contains(name);
        }
        if (owner.equals("org.apache.hadoop.hdfs.server.protocol.KeyUpdateCommand")
                || owner.equals("org.apache.hadoop.hdfs.server.protocol.DatanodeRegistration")) {
            return name.startsWith("get") || name.startsWith("set");
        }
        if (owner.equals(HDFS_SASL_CLIENT)) {
            if (name.startsWith("access$")) {
                return true;
            }
            return Arrays.asList("newSocketSend", "peerSend", "socketSend",
                    "checkTrustAndSend", "prepareCheckTrustAndSendForTesting",
                    "prepareSocketSendForTesting",
                    "send", "prepareSendForTesting", "getEncryptedStreams",
                    "prepareEncryptedStreamsForTesting",
                    "getUserNameFromEncryptionKey", "doSaslHandshake")
                    .contains(name);
        }
        if (owner.equals(HDFS_SASL_SERVER)) {
            if (name.startsWith("access$")) {
                return true;
            }
            return Arrays.asList("receive", "getEncryptedStreams",
                    "getSaslStreams", "buildServerPassword",
                    "getEncryptionKeyFromUserName",
                    "getEncryptionKeyFromParsedUserNameForTesting",
                    "receiveEncryptedSaslHandshakeForTesting",
                    "receiveParsedEncryptedSaslHandshakeForTesting",
                    "doSaslHandshake", "deserializeIdentifier").contains(name);
        }
        if (owner.equals(HDFS_SASL_SERVER + "$SaslServerCallbackHandler")) {
            return "handle".equals(name);
        }
        if (owner.startsWith(HDFS_SASL_SERVER + "$")) {
            return "apply".equals(name);
        }
        return false;
    }

    private Set<String> findCandidateClasses() throws IOException {
        Set<String> sourceClasses = sourceClassesTouchingSeeds();
        Set<String> candidates = new LinkedHashSet<>();
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            String className = sootClass.getName();
            if (classNameTouchesSeed(className)
                    || sourceClassMatches(sourceClasses, className)
                    || (sourceClasses.isEmpty() && classFieldsTouchSeed(sootClass))
                    || (target.exceptionSeeded() && sourceClasses.isEmpty()
                    && classDirectlyThrowsSeedException(sootClass))) {
                candidates.add(className);
            }
        }
        return candidates;
    }

    private Set<String> sourceClassesTouchingSeeds() throws IOException {
        Set<String> classes = new LinkedHashSet<>();
        List<Path> roots = new ArrayList<>();
        if (Files.isDirectory(target.moduleDir)) {
            roots.add(target.moduleDir);
        }
        if (Files.isDirectory(target.repoRoot) && !target.repoRoot.equals(target.moduleDir)) {
            roots.add(target.repoRoot);
        }
        for (Path root : roots) {
            try (Stream<Path> stream = Files.walk(root)) {
                List<Path> files = stream
                        .filter(path -> Files.isRegularFile(path)
                                && path.toString().endsWith(".java")
                                && path.toString().contains("/src/main/java/"))
                        .collect(Collectors.toList());
                for (Path file : files) {
                    String text = new String(Files.readAllBytes(file), StandardCharsets.UTF_8);
                    if (!sourceMatchesSeedSearch(text)) {
                        continue;
                    }
                    String className = sourceClassName(file);
                    if (className != null) {
                        classes.add(className);
                    }
                }
            }
        }
        return classes;
    }

    private boolean sourceMatchesSeedSearch(String text) {
        if (target.exceptionSeeded()) {
            String simpleName = simpleClassName(target.seedException);
            return Pattern.compile("\\bnew\\s+(?:"
                    + Pattern.quote(target.seedException) + "|"
                    + Pattern.quote(simpleName) + ")\\s*\\(")
                    .matcher(text).find();
        }
        if (target.seedFunction != null && !target.seedFunction.isEmpty()) {
            return sourceContainsFunction(text, target.seedFunction);
        }
        String keyMethodName = target.seedKeyMethodName();
        if (!keyMethodName.isEmpty()) {
            return text.contains(target.seedMapName())
                    && sourceContainsFunction(text, keyMethodName);
        }
        return containsAll(text, target.seedVariables);
    }

    private boolean sourceContainsFunction(String text, String functionName) {
        Pattern pattern = Pattern.compile("\\b" + Pattern.quote(functionName) + "\\s*\\(");
        return pattern.matcher(text).find();
    }

    private String sourceClassName(Path file) {
        String path = file.toString().replace('\\', '/');
        String marker = "/src/main/java/";
        int index = path.indexOf(marker);
        if (index < 0 || !path.endsWith(".java")) {
            return null;
        }
        return path.substring(index + marker.length(), path.length() - ".java".length())
                .replace('/', '.');
    }

    private boolean classNameTouchesSeed(String className) {
        if (target.exceptionSeeded()) {
            return target.seedException.equals(className);
        }
        return containsAny(className, target.seedVariables);
    }

    private boolean sourceClassMatches(Set<String> sourceClasses, String sootClassName) {
        for (String sourceClass : sourceClasses) {
            if (sootClassName.equals(sourceClass)
                    || sootClassName.startsWith(sourceClass + "$")) {
                return true;
            }
        }
        return false;
    }

    private boolean classFieldsTouchSeed(SootClass sootClass) {
        for (SootField field : sootClass.getFields()) {
            if (target.exceptionSeeded()
                    && exceptionTypeMatches(field.getType().toString())) {
                return true;
            }
            if (containsAny(field.getName(), target.seedVariables)
                    || containsAny(field.getSignature(), target.seedVariables)) {
                return true;
            }
        }
        return false;
    }

    private boolean classDirectlyThrowsSeedException(SootClass sootClass) {
        for (SootMethod method : sootClass.getMethods()) {
            if (!method.isConcrete()) {
                continue;
            }
            Body body;
            try {
                body = method.retrieveActiveBody();
            } catch (RuntimeException ignored) {
                continue;
            }
            for (Unit unit : body.getUnits()) {
                if (unit instanceof ThrowStmt
                        && exceptionTypeMatches(((ThrowStmt) unit).getOp()
                        .getType().toString())) {
                    return true;
                }
                if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()) {
                    MethodSig invoked = parseMethodSig(((Stmt) unit).getInvokeExpr()
                            .getMethodRef().getSignature());
                    if (invoked != null && "<init>".equals(invoked.name)
                            && exceptionTypeMatches(invoked.owner)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private void loadClasses(Set<String> classNames) {
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            if (!classNames.contains(sootClass.getName())) {
                continue;
            }
            for (SootMethod method : sootClass.getMethods()) {
                loadMethod(method);
            }
        }
        LOG.info("Loaded {} seed-candidate methods from {} classes",
                factsByMethod.size(), classNames.size());
    }

    private void loadStaticPortMappingClasses() {
        if (staticPortMappings.isEmpty()) {
            return;
        }
        int before = factsByMethod.size();
        loadClassFamily(HDFS_SASL_CLIENT);
        loadClassFamily(HDFS_SASL_SERVER);
        LOG.info("Loaded {} additional methods for hard-coded data-flow mappings",
                factsByMethod.size() - before);
    }

    private void loadClassFamily(String className) {
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            String current = sootClass.getName();
            if (!current.equals(className) && !current.startsWith(className + "$")) {
                continue;
            }
            for (SootMethod method : sootClass.getMethods()) {
                loadMethod(method);
            }
        }
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
            if (fact.invoke != null) {
                callersByCallee.computeIfAbsent(fact.invoke,
                        ignored -> new ArrayList<>()).add(fact);
            }
        }
        factsByMethod.put(method.getSignature(), facts);
        methodsBySignature.put(method.getSignature(), method);
        return true;
    }

    private void initializeSeedAnchors() {
        for (Map.Entry<String, List<Fact>> entry : factsByMethod.entrySet()) {
            String method = entry.getKey();
            if (!methodMatchesSeedFunction(method)) {
                continue;
            }
            List<Fact> facts = entry.getValue();
            for (int i = 0; i < facts.size(); i++) {
                Fact fact = facts.get(i);
                if (!isLookupGet(fact)) {
                    continue;
                }
                SeedLookupAnchor anchor = traceLookupToSeedMap(facts, i);
                if (anchor == null) {
                    continue;
                }
                selectedMethods.add(method);
                Set<String> relevant = relevant(method);
                for (Fact fieldFact : anchor.seedFieldFacts) {
                    for (String field : fieldFact.fields) {
                        if (!fieldTouchesSeedMap(field)) {
                            continue;
                        }
                        String node = canonical(method, field);
                        relevant.add(node);
                        addEdge("seed_field", target.seedPredicate(), node,
                                method, fieldFact, "seed map field feeding lookup");
                    }
                }
                for (String value : anchor.seedValues) {
                    String node = canonical(method, value);
                    if (ignoreNode(node)) {
                        continue;
                    }
                    relevant.add(node);
                    addEdge("seed_lookup_operand", target.seedPredicate(), node,
                            method, fact, "lookup operand from seed map/key expression");
                }
            }
        }
        LOG.info("Initialized {} selected methods from seed variables",
                selectedMethods.size());
    }

    private void initializeHdfsDirectLookupSeedAnchors() {
        for (Map.Entry<String, List<Fact>> entry : factsByMethod.entrySet()) {
            String method = entry.getKey();
            MethodSig sig = parseMethodSig(method);
            if (sig == null || !"retrieveDataEncryptionKey".equals(sig.name)) {
                continue;
            }
            List<Fact> facts = entry.getValue();
            for (Fact fact : facts) {
                if (!isLookupGet(fact) || !factFieldsTouchSeedMap(fact)) {
                    continue;
                }
                selectedMethods.add(method);
                Set<String> relevant = relevant(method);
                for (String field : fact.fields) {
                    if (fieldTouchesSeedMap(field)) {
                        String node = canonical(method, field);
                        relevant.add(node);
                        addEdge("seed_field", target.seedPredicate(), node,
                                method, fact, "HDFS direct encryption-key lookup seed map");
                    }
                }
                for (String value : seedLookupValues(fact)) {
                    String node = canonical(method, value);
                    if (ignoreNode(node)) {
                        continue;
                    }
                    relevant.add(node);
                    addEdge("seed_lookup_operand", target.seedPredicate(), node,
                            method, fact, "HDFS direct encryption-key lookup operand");
                }
            }
        }
    }

    /**
     * Discovers the initial backward-slice facts from a target exception.
     *
     * <p>The exception object itself is not treated as an external input.
     * Instead, each direct throw contributes three kinds of evidence: the
     * thrown value, constructor payload values, and CFG guards for which
     * only a subset of successors can reach that throw.  The normal
     * def-use worklist then reduces those local facts to parameters,
     * receiver fields, shared heap, and protocol boundaries.</p>
     */
    private void initializeExceptionSeedAnchors() {
        int seedIndex = 0;
        for (Map.Entry<String, List<Fact>> entry : factsByMethod.entrySet()) {
            String method = entry.getKey();
            List<Fact> facts = entry.getValue();
            for (int throwIndex = 0; throwIndex < facts.size(); throwIndex++) {
                Fact throwFact = facts.get(throwIndex);
                if (!isTargetExceptionThrow(facts, throwIndex)) {
                    continue;
                }

                String exceptionNode = factNode(throwFact) + "#exception:"
                        + target.seedException;
                Set<String> methodRelevant = relevant(method);
                Set<String> throwVariables = new LinkedHashSet<>();
                Set<String> payloadVariables = new LinkedHashSet<>();
                Set<String> guardVariables = new LinkedHashSet<>();
                List<Map<String, Object>> pathGuards = new ArrayList<>();

                ThrowStmt throwStmt = (ThrowStmt) throwFact.unit;
                String thrownValue = canonical(method, throwStmt.getOp().toString());
                if (!ignoreNode(thrownValue)) {
                    methodRelevant.add(thrownValue);
                    throwVariables.add(thrownValue);
                    discoveredExceptionVariables.add(thrownValue);
                    addEdge("seed_exception_throw", thrownValue, exceptionNode,
                            method, throwFact,
                            "direct throw of configured seed exception");
                }

                ExceptionConstruction construction = findExceptionConstruction(
                        facts, throwIndex, throwStmt.getOp().toString());
                if (construction != null) {
                    for (String actual : construction.actuals) {
                        String node = canonical(method, actual);
                        if (ignoreNode(node)) {
                            continue;
                        }
                        methodRelevant.add(node);
                        payloadVariables.add(node);
                        discoveredExceptionVariables.add(node);
                        addEdge("exception_payload_argument", node, exceptionNode,
                                method, construction.fact,
                                "exception constructor payload contributes to thrown value");
                    }
                }

                for (ExceptionGuard guard : controllingGuards(method, throwFact)) {
                    for (String use : causalGuardUses(guard.fact)) {
                        String node = canonical(method, use);
                        if (ignoreNode(node)) {
                            continue;
                        }
                        methodRelevant.add(node);
                        guardVariables.add(node);
                        discoveredExceptionVariables.add(node);
                        addEdge("exception_guard", node, exceptionNode,
                                method, guard.fact,
                                "dominating branch requires Jimple outcome "
                                        + guard.requiredOutcome
                                        + " to reach target throw");
                        Map<String, Object> edge = emittedEdgeRows.get(
                                edgeKey("exception_guard", node,
                                        exceptionNode, method,
                                        guard.fact));
                        if (edge != null) {
                            ControlDependenceEdgeSupport
                                    .annotatePathGuard(edge, method,
                                            guard.fact.unitIndex,
                                            throwFact.unitIndex,
                                            throwFact.unitText,
                                            guard.requiredOutcome,
                                            guard.reachingSuccessorIndices,
                                            node, exceptionNode);
                            guard.branchShape.annotate(edge);
                        }
                    }
                    pathGuards.add(object(
                            "siteId", stableSiteId(method,
                                    guard.fact.unitIndex, "exception_guard"),
                            "line", guard.fact.line,
                            "unitIndex", guard.fact.unitIndex,
                            "jimpleCondition", guard.condition,
                            "requiredOutcome", guard.requiredOutcome,
                            "reachingSuccessorIndices",
                            guard.reachingSuccessorIndices,
                            "branchKind", guard.branchShape.kind,
                            "switchCaseKeys",
                            guard.branchShape.caseKeys,
                            "defaultSuccessorIndex",
                            guard.branchShape.defaultSuccessorIndex,
                            "successorIndexAuthority",
                            "STATIC_BRANCH_CASE_ORDER_THEN_DEFAULT_V1"));
                }

                selectedMethods.add(method);
                discoveredExceptionMethods.add(method);
                discoveredExceptionSeeds.add(object(
                        "id", "seed.exception_site." + seedIndex++,
                        "kind", "discovered_exception_site",
                        "exception", target.seedException,
                        "method", method,
                        "line", throwFact.line,
                        "unitIndex", throwFact.unitIndex,
                        "throwUnit", throwFact.unitText,
                        "throwVariables", new ArrayList<>(throwVariables),
                        "payloadVariables", new ArrayList<>(payloadVariables),
                        "guardVariables", new ArrayList<>(guardVariables),
                        "pathGuards", pathGuards,
                        "authority", "STATIC_EXCEPTION_CAUSALITY"));
            }
        }
        LOG.info("Discovered {} direct throw sites for {} in {} methods",
                discoveredExceptionSeeds.size(), target.seedException,
                discoveredExceptionMethods.size());
    }

    private boolean isTargetExceptionThrow(List<Fact> facts, int throwIndex) {
        Fact fact = facts.get(throwIndex);
        if (!(fact.unit instanceof ThrowStmt)) {
            return false;
        }
        ThrowStmt stmt = (ThrowStmt) fact.unit;
        if (exceptionTypeMatches(stmt.getOp().getType().toString())) {
            return true;
        }
        return findExceptionConstruction(facts, throwIndex,
                stmt.getOp().toString()) != null;
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
        SootMethod sootMethod = methodsBySignature.get(method);
        if (sootMethod == null || targetFact.unit == null) {
            return Collections.emptyList();
        }
        Body body;
        try {
            body = sootMethod.retrieveActiveBody();
        } catch (RuntimeException ignored) {
            return Collections.emptyList();
        }
        UnitGraph graph;
        try {
            graph = new BriefUnitGraph(body);
        } catch (RuntimeException ignored) {
            return Collections.emptyList();
        }
        Set<Unit> dominators = Collections.newSetFromMap(
                new IdentityHashMap<Unit, Boolean>());
        try {
            dominators.addAll(new MHGDominatorsFinder<Unit>(graph)
                    .getDominators(targetFact.unit));
        } catch (RuntimeException ignored) {
            return Collections.emptyList();
        }
        Map<Unit, Fact> factsByUnit = new IdentityHashMap<>();
        for (Fact fact : factsByMethod.getOrDefault(method,
                Collections.emptyList())) {
            factsByUnit.put(fact.unit, fact);
        }
        List<ExceptionGuard> guards = new ArrayList<>();
        for (Fact candidate : factsByMethod.getOrDefault(method,
                Collections.emptyList())) {
            if (!candidate.isBranch || !dominators.contains(candidate.unit)) {
                continue;
            }
            CausynthBranchShape branchShape =
                    CausynthBranchShape.from(body, candidate.unit);
            if (branchShape == null
                    || branchShape.successorCount() < 2) {
                continue;
            }
            List<Unit> successors = branchShape.successors;
            int reachingSuccessors = 0;
            List<Integer> reachingIndices = new ArrayList<>();
            for (int successorIndex = 0;
                 successorIndex < successors.size(); successorIndex++) {
                if (canReachWithoutRevisiting(graph,
                        successors.get(successorIndex), targetFact.unit,
                        candidate.unit)) {
                    reachingSuccessors++;
                    reachingIndices.add(successorIndex);
                }
            }
            if (reachingSuccessors > 0
                    && reachingSuccessors < successors.size()) {
                Fact guard = factsByUnit.get(candidate.unit);
                if (guard != null) {
                    Boolean requiredOutcome = null;
                    String condition = candidate.unitText;
                    if (candidate.unit instanceof IfStmt) {
                        IfStmt ifStmt = (IfStmt) candidate.unit;
                        condition = ifStmt.getCondition().toString();
                        boolean takenReaches = canReachWithoutRevisiting(
                                graph, ifStmt.getTarget(), targetFact.unit,
                                candidate.unit);
                        Unit fallThrough = body.getUnits().getSuccOf(candidate.unit);
                        boolean fallThroughReaches = fallThrough != null
                                && canReachWithoutRevisiting(graph,
                                fallThrough, targetFact.unit,
                                candidate.unit);
                        if (takenReaches != fallThroughReaches) {
                            requiredOutcome = takenReaches;
                        }
                    }
                    guards.add(new ExceptionGuard(guard, condition,
                            requiredOutcome, reachingIndices,
                            branchShape));
                }
            }
        }
        guards.sort(Comparator.comparingInt(guard -> guard.fact.unitIndex));
        List<ExceptionGuard> result = Collections.unmodifiableList(guards);
        requiredPathGuardsByFact.put(cacheKey, result);
        return result;
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

    private boolean canReach(UnitGraph graph, Unit start, Unit targetUnit) {
        Set<Unit> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Deque<Unit> work = new ArrayDeque<>();
        work.add(start);
        while (!work.isEmpty()) {
            Unit current = work.removeFirst();
            if (current == targetUnit) {
                return true;
            }
            if (!seen.add(current)) {
                continue;
            }
            work.addAll(graph.getSuccsOf(current));
        }
        return false;
    }

    private boolean exceptionTypeMatches(String candidateType) {
        if (!target.exceptionSeeded() || candidateType == null) {
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

    private Collection<SootMethod> methodsForStaticIndex() {
        // The HDFS fast path bounds which bodies are retained as working
        // facts, not which application methods may write a shared field
        // or call a selected writer.  Restricting this index to the
        // current factsByMethod keys makes the first index build a
        // permanent under-approximation: a writer such as
        // DatanodeDescriptor.setNeedKeyUpdate and its Monitor.run caller
        // can never be discovered later because the index is one-shot.
        // factsFromMethod is deliberately ephemeral below, so scanning
        // the complete application method catalog does not turn the
        // scoped working set into a whole-program retained-facts set.
        return methodsBySignature.values();
    }

    private boolean methodMatchesSeedFunction(String method) {
        if (target.seedFunction == null || target.seedFunction.isEmpty()) {
            return true;
        }
        MethodSig sig = parseMethodSig(method);
        return sig != null && target.seedFunction.equals(sig.name);
    }

    private boolean factTouchesSeed(Fact fact) {
        String text = fact.method + " " + fact.unitText + " " + fact.fields;
        return containsAny(text, target.seedVariables);
    }

    private boolean isLookupGet(Fact fact) {
        MethodSig sig = parseMethodSig(fact.invoke);
        if (sig == null) {
            return false;
        }
        return "get".equals(sig.name) && sig.params.size() == 1;
    }

    private List<String> seedLookupValues(Fact fact) {
        List<String> values = new ArrayList<>();
        values.addAll(fact.defs);
        values.addAll(nonInvokeUses(fact));
        values.addAll(fact.fields);
        values.addAll(actualInvokeArgs(fact.unitText));
        return values;
    }

    private SeedLookupAnchor traceLookupToSeedMap(List<Fact> facts, int lookupIndex) {
        Fact lookup = facts.get(lookupIndex);
        List<Fact> seedFieldFacts = new ArrayList<>();
        Set<String> seedValues = new LinkedHashSet<>(seedLookupValues(lookup));
        boolean mapMatched = false;
        if (factFieldsTouchSeedMap(lookup)) {
            seedFieldFacts.add(lookup);
            mapMatched = true;
        }

        Set<String> work = new LinkedHashSet<>();
        String baseLocal = invokeBaseLocal(lookup.unitText);
        if (baseLocal != null) {
            work.add(baseLocal);
        } else {
            work.addAll(localNames(nonInvokeUses(lookup)));
        }
        if (work.isEmpty()) {
            return null;
        }

        if (!mapMatched) {
            for (int i = lookupIndex - 1; i >= 0; i--) {
                Fact fact = facts.get(i);
                Set<String> defs = localNames(fact.defs);
                if (!intersectsLocal(work, defs)) {
                    continue;
                }
                seedValues.addAll(fact.defs);
                seedValues.addAll(nonInvokeUses(fact));
                seedValues.addAll(fact.fields);
                if (factFieldsTouchSeedMap(fact)) {
                    seedFieldFacts.add(fact);
                    mapMatched = true;
                    break;
                }
                work.addAll(localNames(nonInvokeUses(fact)));
            }
        }
        if (!mapMatched || !traceLookupKeyToSeedExpression(facts, lookupIndex, seedValues)) {
            return null;
        }
        return new SeedLookupAnchor(seedFieldFacts, seedValues);
    }

    private boolean traceLookupKeyToSeedExpression(List<Fact> facts, int lookupIndex,
                                                   Set<String> seedValues) {
        String keyMethod = target.seedKeyMethodName();
        if (keyMethod.isEmpty()) {
            return true;
        }
        Set<String> work = localNames(actualInvokeArgs(facts.get(lookupIndex).unitText));
        if (work.isEmpty()) {
            return false;
        }
        for (int i = lookupIndex - 1; i >= 0; i--) {
            Fact fact = facts.get(i);
            Set<String> defs = localNames(fact.defs);
            if (!intersectsLocal(work, defs)) {
                continue;
            }
            seedValues.addAll(fact.defs);
            seedValues.addAll(nonInvokeUses(fact));
            seedValues.addAll(fact.fields);
            seedValues.addAll(actualInvokeArgs(fact.unitText));
            if (factInvokesSeedKeyMethod(fact, keyMethod)) {
                return true;
            }
            work.addAll(localNames(nonInvokeUses(fact)));
            work.addAll(localNames(actualInvokeArgs(fact.unitText)));
        }
        return false;
    }

    private boolean factInvokesSeedKeyMethod(Fact fact, String keyMethod) {
        MethodSig sig = parseMethodSig(fact.invoke);
        return sig != null && keyMethod.equals(sig.name);
    }

    private boolean factFieldsTouchSeedMap(Fact fact) {
        for (String field : fact.fields) {
            if (fieldTouchesSeedMap(field)) {
                return true;
            }
        }
        return false;
    }

    private boolean fieldTouchesSeedMap(String field) {
        return !target.seedVariables.isEmpty()
                && field != null
                && field.contains(target.seedVariables.get(0));
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
        if (trimmed.matches("[$]?[A-Za-z_][A-Za-z0-9_]*")) {
            return trimmed;
        }
        Matcher cast = Pattern.compile("\\)\\s*([$]?[A-Za-z_][A-Za-z0-9_]*)$")
                .matcher(trimmed);
        if (trimmed.startsWith("(") && cast.find()) {
            return cast.group(1);
        }
        return null;
    }

    private String invokeBaseLocal(String unitText) {
        Matcher matcher = Pattern.compile("(?:virtualinvoke|interfaceinvoke|specialinvoke)\\s+"
                + "([$]?[A-Za-z_][A-Za-z0-9_]*)\\.<").matcher(unitText);
        if (matcher.find()) {
            return matcher.group(1);
        }
        return null;
    }

    private void runWorklist() {
        for (int round = 0; round < MAX_ROUNDS && edges.size() < maxEdges; round++) {
            boolean changed = false;
            List<String> methodsThisRound = new ArrayList<>(selectedMethods);
            for (String method : methodsThisRound) {
                changed |= processMethod(method);
                changed |= expandCallers(method);
                changed |= expandRpcCallers(method);
                changed |= expandDispatchCallers(method);
                changed |= expandStaticPortMappings(method);
                changed |= expandFieldWriters(method);
                changed |= expandConstructorCallers(method);
                changed |= expandMethodCallers(method);
                // maxMethods limits admission of new static candidates;
                // it must not prevent already admitted methods from
                // reaching their fixed point.  The previous early break
                // left the tail of selectedMethods unprocessed whenever
                // the cap was reached (trace-visible methods could then
                // have zero data-flow edges).
                if (edges.size() >= maxEdges) {
                    break;
                }
            }
            changed |= propagateProjectedEdgesFromExistingEdges();
            if (!changed) {
                break;
            }
        }
    }

    private boolean processMethod(String method) {
        List<Fact> facts = factsByMethod.get(method);
        if (facts == null) {
            return false;
        }
        boolean changed = false;
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
                changed |= promoteArrayContainerForProjectedElementRead(
                        method, fact, relevant);
            }
            boolean defHit = defExactHit || defProjectionHit;
            boolean useExactHit = exactIntersects(relevant, uses);
            boolean useProjectionHit = projectionIntersects(relevant, uses);
            boolean useHit = useExactHit || useProjectionHit;
            if (defHit || useHit) {
                for (String def : defs) {
                    for (String use : uses) {
                        if (ignoreNode(def) || ignoreNode(use)) {
                            continue;
                        }
                        if (addEdge("local_def_use", use, def, method, fact,
                                "Jimple use/field/argument flows to def")) {
                            changed = true;
                        }
                    }
                }
                if (defExactHit) {
                    for (String use : uses) {
                        changed |= relevant.add(use);
                    }
                }
                if (useHit) {
                    for (String def : defs) {
                        changed |= relevant.add(def);
                    }
                }
            }

            if (defExactHit) {
                changed |= processRequiredPathGuards(method, fact, defs,
                        relevant);
            }

            if (fact.isBranch && useExactHit) {
                for (String use : uses) {
                    changed |= addEdge("guard_dependency", use, factNode(fact),
                            method, fact, "branch consumes relevant value");
                }
            }
            if (fact.isThrow && useExactHit) {
                for (String use : uses) {
                    changed |= addEdge("throw_dependency", use, factNode(fact),
                            method, fact, "throw consumes relevant value");
                }
            }
            changed |= processFieldReads(method, fact, defs, relevant);
            changed |= processFieldWrites(method, facts, fact, relevant);
            changed |= processInvoke(method, fact, defs, uses, relevant);
        }
        return changed;
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
    private boolean promoteArrayContainerForProjectedElementRead(
            String method, Fact fact, Set<String> relevant) {
        if (!(fact.unit instanceof AssignStmt)) {
            return false;
        }
        Value right = ((AssignStmt) fact.unit).getRightOp();
        if (!(right instanceof ArrayRef)) {
            return false;
        }
        String base = canonical(method,
                ((ArrayRef) right).getBase().toString());
        return !ignoreNode(base) && relevant.add(base);
    }

    /**
     * Adds intraprocedural control dependencies for a statement that
     * defines an exactly relevant value.  This keeps the old def-use
     * worklist intact while allowing it to cross Jimple's branch-based
     * lowering of expressions such as {@code Time.now() > expiryDate}.
     */
    private boolean processRequiredPathGuards(String method, Fact targetFact,
                                              List<String> defs,
                                              Set<String> relevant) {
        if (targetFact.isBranch) {
            return false;
        }
        List<String> relevantDefs = new ArrayList<>();
        for (String def : defs) {
            if (relevant.contains(def) && !ignoreNode(def)) {
                relevantDefs.add(def);
            }
        }
        if (relevantDefs.isEmpty()) {
            return false;
        }

        boolean changed = false;
        for (ExceptionGuard guard : controllingGuards(method, targetFact)) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(method, use);
                if (ignoreNode(guardNode)) {
                    continue;
                }
                for (String def : relevantDefs) {
                    changed |= addEdge(
                            ControlDependenceEdgeSupport.PATH_GUARD_KIND,
                            guardNode, def, method, guard.fact,
                            "dominating branch requires Jimple outcome "
                                    + guard.requiredOutcome
                                    + " to reach relevant definition at u"
                                    + targetFact.unitIndex);
                    Map<String, Object> edge = emittedEdgeRows.get(edgeKey(
                            ControlDependenceEdgeSupport.PATH_GUARD_KIND,
                            guardNode, def, method, guard.fact));
                    if (edge != null) {
                        ControlDependenceEdgeSupport.annotatePathGuard(
                                edge, method, guard.fact.unitIndex,
                                targetFact.unitIndex,
                                targetFact.unitText,
                                guard.requiredOutcome,
                                guard.reachingSuccessorIndices,
                                guardNode, def);
                        guard.branchShape.annotate(edge);
                    }
                }
                changed |= relevant.add(guardNode);
            }
        }
        return changed;
    }

    private boolean processFieldReads(String method, Fact fact, List<String> defs,
                                      Set<String> relevant) {
        boolean changed = false;
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
                if (addEdge("field_read", fieldNode, def, method, fact,
                        "field value flows to local/return")) {
                    changed = true;
                }
                annotateDirectDeclaredFieldEdge("field_read", fieldNode,
                        def, method, fact, field);
            }
            if (defExactHit && canOpenFieldFromPlainValues(defs)) {
                changed |= relevant.add(fieldNode);
            }
        }
        for (InstanceFieldAccess access : fact.instanceFieldUses) {
            String fieldName = fieldNameFromSignature(access.field);
            String receiverField = fieldProjection(canonical(method, access.base), fieldName);
            if (ignoreNode(receiverField)) {
                continue;
            }
            String classField = canonical(method, access.field);
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
                if (addEdge("instance_field_read", receiverField, def, method, fact,
                        "receiver field value flows to local/return")) {
                    changed = true;
                }
                annotateDirectDeclaredFieldEdge("instance_field_read",
                        receiverField, def, method, fact, access.field);
            }
            if (defExactHit && canOpenFieldFromPlainValues(defs)) {
                changed |= relevant.add(receiverField);
            }
        }
        return changed;
    }

    private boolean processFieldWrites(String method, List<Fact> facts, Fact fact,
                                       Set<String> relevant) {
        boolean changed = false;
        for (String field : fact.fieldDefs) {
            changed |= processFieldWrite(method, fact, relevant, field,
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
                for (String source : sources) {
                    if (ignoreNode(source)) {
                        continue;
                    }
                    if (addEdge("instance_field_write", source, receiverField, method,
                            fact, "assignment writes receiver field")) {
                        changed = true;
                    }
                    // A receiver-sensitive write also updates the declared
                    // class field.  Preserve both views: the receiver
                    // projection lets runtime match object identity, while
                    // the class-field node connects possible writers and
                    // readers across threads before identities are known.
                    if (addEdge("field_write", source, classField, method,
                            fact, "receiver assignment writes declared field")) {
                        changed = true;
                    }
                    changed |= relevant.add(classField);
                    if ((receiverExactHit || classFieldHit)
                            && canOpenFieldFromPlainValue(source)) {
                        changed |= relevant.add(source);
                    }
                }
            }
        }
        for (String mutatedField : fieldsMutatedByInvoke(facts, fact.unitIndex)) {
            String mutatedFieldNode = canonical(method, mutatedField);
            boolean mutationAffectsRelevantState =
                    relevant.contains(mutatedFieldNode);
            changed |= processFieldWrite(method, fact, relevant, mutatedField,
                    fieldMutationSources(method, fact, mutatedField),
                    "field_mutation",
                    "mutator call updates object stored in relevant field");
            if (mutationAffectsRelevantState) {
                changed |= processHeapMutationPathGuards(method, fact,
                        mutatedFieldNode, relevant);
            }
        }
        return changed;
    }

    /**
     * A heap mutation has no Jimple definition local, so the ordinary
     * {@link #processRequiredPathGuards(String, Fact, List, Set)} path
     * cannot attach the branches that make the mutation execute.  Treat
     * the mutated heap cell as the definition for control-dependence
     * purposes.  This is required for conditional collection updates,
     * including an {@code Iterator.remove()} guarded by a predicate.
     */
    private boolean processHeapMutationPathGuards(
            String method, Fact mutation, String mutatedCell,
            Set<String> relevant) {
        if (ignoreNode(mutatedCell)) {
            return false;
        }
        boolean changed = false;
        for (ExceptionGuard guard : controllingGuards(method, mutation)) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(method, use);
                if (ignoreNode(guardNode)) {
                    continue;
                }
                changed |= addHeapMutationPathGuardEdge(guardNode,
                        mutatedCell, method, guard, mutation);
                changed |= relevant.add(guardNode);
            }
        }
        return changed;
    }

    private boolean addHeapMutationPathGuardEdge(
            String guardNode, String mutatedCell, String method,
            ExceptionGuard guard, Fact mutation) {
        String evidence = "dominating branch requires Jimple outcome "
                + guard.requiredOutcome + " to reach heap mutation at u"
                + mutation.unitIndex;
        boolean changed = addEdge("heap_mutation_path_guard", guardNode,
                mutatedCell, method, guard.fact, evidence);
        String key = edgeKey("heap_mutation_path_guard", guardNode,
                mutatedCell, method, guard.fact);
        Map<String, Object> edge = emittedEdgeRows.get(key);
        if (edge == null) {
            return changed;
        }
        boolean annotated = ControlDependenceEdgeSupport
                .annotateGuardedMutation(
                edge, method, guard.fact.unitIndex, mutation.unitIndex,
                guard.requiredOutcome, guard.reachingSuccessorIndices);
        guard.branchShape.annotate(edge);
        return annotated || changed;
    }

    private boolean processFieldWrite(String method, Fact fact, Set<String> relevant,
                                      String field, List<String> sources, String kind,
                                      String evidence) {
        String fieldNode = canonical(method, field);
        if (ignoreNode(fieldNode)) {
            return false;
        }
        boolean fieldHit = relevant.contains(fieldNode);
        if (!fieldHit) {
            return false;
        }
        boolean changed = false;
        if (sources.isEmpty()) {
            sources = Collections.singletonList(factNode(fact));
        }
        for (String source : sources) {
            if (ignoreNode(source)) {
                continue;
            }
            if (addEdge(kind, source, fieldNode, method, fact, evidence)) {
                changed = true;
            }
            if (fieldHit && canOpenFieldFromPlainValue(source)) {
                changed |= relevant.add(source);
            }
        }
        return changed;
    }

    private boolean expandFieldWriters(String method) {
        List<String> fields = relevant(method).stream()
                .filter(this::isApplicationField)
                .collect(Collectors.toList());
        if (fields.isEmpty()) {
            return false;
        }
        buildGlobalStaticIndex();
        boolean changed = false;
        for (String field : fields) {
            if (!expandedFieldWriterFields.add(field)) {
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
                if (writerMethod != null && loadMethod(writerMethod)) {
                    changed = true;
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
                    if (addEdge(writer.kind, source, writer.field, writer.method,
                            writer.fact, writer.evidence)) {
                        changed = true;
                    }
                    if (canOpenFieldFromPlainValue(source)) {
                        changed |= writerRelevant.add(source);
                    }
                }
            }
        }
        return changed;
    }

    private boolean expandConstructorCallers(String method) {
        List<ConstructorParam> params = relevant(method).stream()
                .map(this::constructorParam)
                .filter(param -> param != null)
                .collect(Collectors.toList());
        String thisNode = methodThisNode(method);
        Set<String> thisProjectionSuffixes = projectionSuffixesForBase(method, thisNode);
        if (params.isEmpty() && thisProjectionSuffixes.isEmpty()) {
            return false;
        }
        buildGlobalStaticIndex();
        boolean changed = false;
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
                    changed |= expandConstructorReceiverFields(method, thisNode,
                            thisProjectionSuffixes, callsite);
                }
            }
        }
        for (ConstructorParam param : params) {
            String expansionKey = param.constructor + "#" + param.index;
            if (!expandedConstructorCallees.add(expansionKey)) {
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
                if (callerMethod != null && loadMethod(callerMethod)) {
                    changed = true;
                }
                if (addEdge("constructor_caller_argument", actual, param.formal,
                        callsite.method, callsite.fact,
                        "constructor caller actual reaches relevant constructor formal")) {
                    changed = true;
                }
                changed |= relevant(callsite.method).add(actual);
                changed |= selectedMethods.add(callsite.method);
            }
        }
        return changed;
    }

    private boolean expandMethodCallers(String method) {
        MethodSig callee = parseMethodSig(method);
        if (callee == null || "<init>".equals(callee.name)
                || "<clinit>".equals(callee.name)
                || !isApplicationClassName(callee.owner)) {
            return false;
        }
        Set<String> calleeRelevant = relevant(method);
        String thisNode = methodThisNode(method);
        Set<String> thisProjectionSuffixes = projectionSuffixesForBase(method, thisNode);
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
            return false;
        }

        buildGlobalStaticIndex();
        List<MethodCallsite> callsites = methodCallersByCallee.get(method);
        if (callsites == null || callsites.isEmpty()) {
            return false;
        }

        boolean changed = false;
        int count = 0;
        for (MethodCallsite callsite : callsites) {
            if (count++ >= MAX_METHOD_CALLERS_PER_METHOD
                    || selectedMethods.size() >= maxMethods
                    || edges.size() >= maxEdges) {
                break;
            }
            SootMethod callerMethod = methodsBySignature.get(callsite.method);
            if (callerMethod != null && loadMethod(callerMethod)) {
                changed = true;
            }
            Set<String> callerRelevant = relevant(callsite.method);
            for (int index : relevantParams) {
                String expansionKey = method + "#param" + index + "@" + callsite.method
                        + "#" + callsite.fact.unitIndex;
                if (!expandedMethodCallerKeys.add(expansionKey)
                        || index >= callsite.actuals.size()) {
                    continue;
                }
                String actual = callsite.actuals.get(index);
                if (ignoreNode(actual)) {
                    changed |= addTypedLiteralCallerArgument(callee,
                            index, callsite);
                    if (isTypedLiteralArgument(callsite.fact, index,
                            callee.params.get(index))) {
                        changed |= selectedMethods.add(callsite.method);
                    }
                    continue;
                }
                if (addEdge("method_caller_argument", actual,
                        formalParam(callee, index), callsite.method, callsite.fact,
                        "method caller actual reaches relevant callee formal")) {
                    changed = true;
                }
                changed |= callerRelevant.add(actual);
                changed |= selectedMethods.add(callsite.method);
            }
            changed |= addReceiverFieldEffectPathGuards(method,
                    callsite, callerRelevant);
            if (thisRelevant) {
                changed |= expandMethodReceiverFields(method, thisNode,
                        thisProjectionSuffixes, callsite);
            }
            if (returnRelevant) {
                changed |= expandCallerReturn("method_caller_return",
                        returnNode, callsite.defs, callsite.method,
                        callsite.fact, callerRelevant,
                        "method caller receives relevant callee return");
            }
        }
        return changed;
    }

    /**
     * Retains a constant actual without turning a naked Jimple literal
     * into a symbolic live-in.  The cell is the exact callsite fact (an
     * internal expression understood by the region planner); the typed
     * literal and parameter position are authoritative edge metadata.
     * This matters for setters such as setNeedKeyUpdate(true), where the
     * value is fixed but whether the call executes is path dependent.
     */
    private boolean addTypedLiteralCallerArgument(MethodSig callee,
                                                  int argumentIndex,
                                                  MethodCallsite callsite) {
        Value literal = invokeArgument(callsite.fact, argumentIndex);
        if (!(literal instanceof Constant)
                || argumentIndex < 0
                || argumentIndex >= callee.params.size()) {
            return false;
        }
        String formalType = callee.params.get(argumentIndex);
        String literalValue = typedLiteralValue(literal, formalType);
        if (literalValue.isEmpty()) {
            return false;
        }
        String source = factNode(callsite.fact);
        String target = formalParam(callee, argumentIndex);
        boolean changed = addEdge("method_caller_literal_argument",
                source, target, callsite.method, callsite.fact,
                "exact callsite supplies a typed literal to relevant callee formal");
        Map<String, Object> edge = emittedEdgeRows.get(edgeKey(
                "method_caller_literal_argument", source, target,
                callsite.method, callsite.fact));
        if (edge != null) {
            edge.put("argumentIndex", argumentIndex);
            edge.put("literalJavaType", formalType);
            edge.put("literalValue", literalValue);
            edge.put("literalAuthority",
                    "JIMPLE_TYPED_CONSTANT_AT_EXACT_CALLSITE_V1");
            edge.put("literalIsSymbolicInput", false);
            edge.put("calleeMethod", callee.raw);
            edge.put("effectSiteId", stableSiteId(callsite.method,
                    callsite.fact.unitIndex,
                    "method_receiver_field_effect"));
        }
        return changed;
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
    private boolean addReceiverFieldEffectPathGuards(
            String calleeMethod, MethodCallsite callsite,
            Set<String> callerRelevant) {
        Set<String> effectFields = relevantFieldEffectsByMethod.get(
                calleeMethod);
        if (effectFields == null || effectFields.isEmpty()) {
            return false;
        }
        boolean changed = false;
        for (ExceptionGuard guard : controllingGuards(callsite.method,
                callsite.fact)) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(callsite.method, use);
                if (ignoreNode(guardNode)) {
                    continue;
                }
                for (String effectField : effectFields) {
                    changed |= addReceiverFieldEffectPathGuardEdge(
                            guardNode, effectField, calleeMethod,
                            callsite, guard);
                }
                changed |= callerRelevant.add(guardNode);
                changed |= selectedMethods.add(callsite.method);
            }
        }
        return changed;
    }

    private boolean addReceiverFieldEffectPathGuardEdge(
            String guardNode, String effectField, String calleeMethod,
            MethodCallsite callsite, ExceptionGuard guard) {
        String kind = "receiver_field_effect_path_guard";
        boolean changed = addEdge(kind, guardNode, effectField,
                callsite.method, guard.fact,
                "dominating branch controls relevant receiver field effect at call u"
                        + callsite.fact.unitIndex);
        Map<String, Object> edge = emittedEdgeRows.get(edgeKey(kind,
                guardNode, effectField, callsite.method, guard.fact));
        if (edge == null) {
            return changed;
        }
        boolean annotated = ControlDependenceEdgeSupport
                .annotateGuardedReceiverEffect(
                edge, callsite.method, guard.fact.unitIndex,
                callsite.fact.unitIndex, guard.requiredOutcome,
                guard.reachingSuccessorIndices, calleeMethod,
                effectField);
        guard.branchShape.annotate(edge);
        return annotated || changed;
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
        Matcher matcher = Pattern.compile(">\\.param(\\d+):").matcher(node);
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
        for (SootMethod method : methodsForStaticIndex()) {
            if (!method.isConcrete()
                    || !method.getDeclaringClass().isApplicationClass()) {
                continue;
            }
            globalStaticIndexCandidateMethodCount++;
            List<Fact> facts = factsByMethod.get(method.getSignature());
            if (facts == null) {
                facts = factsFromMethod(method);
            }
            if (facts.isEmpty()) {
                globalStaticIndexUnreadableMethodCount++;
                continue;
            }
            globalStaticIndexIndexedMethodCount++;
            for (FieldWrite write : fieldWritesInMethod(method.getSignature(), facts)) {
                addIndexedFieldWrite(write);
            }
            for (ConstructorCallsite callsite : constructorCallsitesInMethod(
                    method.getSignature(), facts)) {
                addIndexedConstructorCallsite(callsite);
            }
            for (MethodCallsite callsite : methodCallsitesInMethod(
                    method.getSignature(), facts)) {
                addIndexedMethodCallsite(callsite);
            }
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
        } else {
            truncatedFieldWriterIndexFields.add(write.field);
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
        } else {
            truncatedMethodCallerIndexMethods.add(callsite.callee);
        }
    }

    private List<FieldWrite> fieldWritesInMethod(String method, List<Fact> facts) {
        List<FieldWrite> writes = new ArrayList<>();
        for (Fact fact : facts) {
            for (String field : fact.fieldDefs) {
                writes.add(new FieldWrite(method, field, fact, "field_write",
                        fieldWriteSources(method, fact, field),
                        "assignment writes field"));
            }
            for (String mutatedField : fieldsMutatedByInvoke(facts, fact.unitIndex)) {
                writes.add(new FieldWrite(method, mutatedField, fact, "field_mutation",
                        fieldMutationSources(method, fact, mutatedField),
                        "mutator call updates object stored in field"));
            }
        }
        return writes;
    }

    private List<ConstructorCallsite> constructorCallsitesInMethod(String method,
                                                                   List<Fact> facts) {
        List<ConstructorCallsite> callsites = new ArrayList<>();
        for (Fact fact : facts) {
            MethodSig sig = parseMethodSig(fact.invoke);
            if (sig == null || !"<init>".equals(sig.name)
                    || !isApplicationClassName(sig.owner)) {
                continue;
            }
            callsites.add(new ConstructorCallsite(method, sig.raw, fact,
                    canonical(method, invokeBaseLocal(fact.unitText)),
                    canonicalPositionList(method, actualInvokeArgs(fact.unitText))));
        }
        return callsites;
    }

    private List<MethodCallsite> methodCallsitesInMethod(String method,
                                                         List<Fact> facts) {
        List<MethodCallsite> callsites = new ArrayList<>();
        for (Fact fact : facts) {
            MethodSig sig = parseMethodSig(fact.invoke);
            if (sig == null || "<init>".equals(sig.name)
                    || "<clinit>".equals(sig.name)
                    || !isApplicationClassName(sig.owner)) {
                continue;
            }
            callsites.add(new MethodCallsite(method, sig.raw, fact,
                    canonical(method, invokeBaseLocal(fact.unitText)),
                    canonicalPositionList(method, actualInvokeArgs(fact.unitText)),
                    canonicalList(method, fact.defs)));
        }
        return callsites;
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
        return Pattern.compile("<[^:]+:\\s+.+\\s+[^\\s()]+>")
                .matcher(value).matches();
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

    private boolean processInvoke(String callerMethod, Fact fact, List<String> defs,
                                  List<String> uses, Set<String> callerRelevant) {
        MethodSig callee = parseMethodSig(fact.invoke);
        if (callee == null) {
            return false;
        }
        boolean changed = false;
        changed |= processSemanticMapLookup(callerMethod, fact, callee, defs,
                callerRelevant);
        changed |= processSemanticContainerProjection(callerMethod, fact,
                callee, defs, callerRelevant);
        changed |= processAccessorInvoke(callerMethod, fact, callee, defs,
                callerRelevant);
        List<String> actuals = canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText));
        changed |= processConstructorObjectInvoke(callerMethod, fact, callee,
                actuals, callerRelevant);
        boolean dynamicDispatch = !resolveDispatchTargets(callee)
                .isEmpty();
        boolean expandableCallee = isExpandableMethod(callee.raw);
        SootMethod calleeMethod = expandableCallee ? methodsBySignature.get(callee.raw) : null;
        boolean runtimeRecursiveCaller =
                runtimeRecursiveMethods.contains(callerMethod);
        if (expandableCallee && (selectedMethods.size() < maxMethods
                || runtimeRecursiveMethods.contains(callee.raw))) {
            loadMethod(calleeMethod);
        }
        Set<String> calleeRelevant = expandableCallee
                ? relevantByMethod.computeIfAbsent(callee.raw,
                ignored -> new LinkedHashSet<>())
                : Collections.emptySet();
        if (expandableCallee) {
            changed |= processReceiverSideEffectInvoke(callerMethod, fact,
                    callee, callerRelevant, calleeRelevant);
        }

        for (int i = 0; i < actuals.size() && i < callee.params.size(); i++) {
            String actual = actuals.get(i);
            if (ignoreNode(actual)) {
                continue;
            }
            String formal = formalParam(callee, i);
            boolean formalExactHit = expandableCallee && calleeRelevant.contains(formal);
            boolean formalProjectionHit = expandableCallee
                    && containsProjection(calleeRelevant, formal);
            boolean formalHit = formalExactHit || formalProjectionHit;
            boolean actualExactHit = callerRelevant.contains(actual);
            boolean actualProjectionHit = containsProjection(callerRelevant, actual);
            boolean actualHit = actualExactHit || actualProjectionHit;
            if (!dynamicDispatch && (formalHit || actualHit)) {
                if (addEdge("call_argument", actual, formal, callerMethod, fact,
                        "method call actual flows to callee formal")) {
                    changed = true;
                }
                if (formalExactHit) {
                    changed |= callerRelevant.add(actual);
                }
                if (actualHit && expandableCallee) {
                    changed |= calleeRelevant.add(formal);
                    changed |= selectedMethods.add(callee.raw);
                }
            }
        }

        for (String def : defs) {
            String returnNode = callee.raw + ".return";
            boolean defExactHit = callerRelevant.contains(def);
            boolean defProjectionHit = containsProjection(callerRelevant, def);
            boolean defHit = defExactHit || defProjectionHit;
            if (!dynamicDispatch && defHit) {
                if (addEdge("call_return", returnNode, def, callerMethod, fact,
                        "callee return flows to caller local")) {
                    changed = true;
                }
                if ((defExactHit || defProjectionHit) && expandableCallee) {
                    changed |= calleeRelevant.add(returnNode);
                    changed |= selectedMethods.add(callee.raw);
                }
            }
        }
        if (expandableCallee && runtimeRecursiveCaller
                && selectedMethods.contains(callee.raw)
                && !calleeRelevant.isEmpty()) {
            admitRuntimeRecursiveMethod(callee.raw,
                    stableSiteId(callerMethod, fact.unitIndex,
                            "runtime_recursive_call"));
        }
        changed |= processRpcInvoke(callerMethod, fact, callee, defs, actuals,
                callerRelevant);
        changed |= processDispatchInvoke(callerMethod, fact, callee, defs, actuals,
                callerRelevant);
        return changed;
    }

    /**
     * Closes the receiver dependency of the small Java collection API
     * surface whose result is specified in terms of the receiver's
     * elements.  Generic invoke handling deliberately excludes library
     * receivers: an arbitrary instance method need not return anything
     * derived from its receiver.  That conservative rule, however, loses
     * the exact chain in code such as
     * {@code map.values().toArray(new Value[0])} and can make an output
     * slice appear independent of {@code map}.
     *
     * <p>Only exact, signature-checked Map view factories and Collection
     * {@code toArray} overloads are admitted.  The edge records element
     * identity flow, not container equality or iteration order.  Concrete
     * ordering and cardinality remain runtime refinement obligations.</p>
     */
    private boolean processSemanticContainerProjection(
            String callerMethod, Fact fact, MethodSig callee,
            List<String> defs, Set<String> callerRelevant) {
        String operation = semanticContainerProjectionOperation(callee);
        if (operation.isEmpty() || defs.isEmpty()) {
            return false;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) {
            return false;
        }
        String receiverNode = canonical(callerMethod, receiver);
        if (ignoreNode(receiverNode)) {
            return false;
        }

        boolean changed = false;
        for (String def : defs) {
            boolean defHit = callerRelevant.contains(def)
                    || containsProjection(callerRelevant, def);
            if (!defHit || ignoreNode(def)) {
                continue;
            }
            String kind = "COLLECTION_TO_ARRAY".equals(operation)
                    ? "container_snapshot_projection"
                    : "container_backed_view_projection";
            changed |= addEdgeInternal(kind, receiverNode, def,
                    callerMethod, fact,
                    "Java collection contract makes result elements "
                            + "depend on receiver elements", false);
            Map<String, Object> edge = emittedEdgeRows.get(edgeKey(kind,
                    receiverNode, def, callerMethod, fact));
            if (edge != null) {
                edge.put("containerProjectionContractVersion", 1);
                edge.put("containerProjectionOperation", operation);
                edge.put("containerProjectionAuthority",
                        "JAVA_COLLECTION_API_EXACT_SIGNATURE_WHITELIST_V1");
                edge.put("receiverValueDependencyComplete", true);
                edge.put("elementRelation",
                        semanticContainerElementRelation(operation));
                edge.put("elementIdentityPreserving",
                        !"MAP_ENTRY_SET_VIEW".equals(operation));
                edge.put("mappingAssociationPreserving",
                        "MAP_ENTRY_SET_VIEW".equals(operation));
                edge.put("backedView", !"COLLECTION_TO_ARRAY".equals(
                        operation));
                edge.put("snapshot", "COLLECTION_TO_ARRAY".equals(
                        operation));
                edge.put("containerEqualityAsserted", false);
                edge.put("iterationOrderAuthority",
                        "RUNTIME_REFINEMENT_REQUIRED");
            }
            changed |= callerRelevant.add(receiverNode);
        }
        return changed;
    }

    private String semanticContainerElementRelation(String operation) {
        if ("MAP_VALUES_VIEW".equals(operation)) {
            return "MAP_VALUE_REFERENCE_IDENTITY";
        }
        if ("MAP_KEY_SET_VIEW".equals(operation)) {
            return "MAP_KEY_REFERENCE_IDENTITY";
        }
        if ("MAP_ENTRY_SET_VIEW".equals(operation)) {
            return "MAP_ENTRY_KEY_VALUE_ASSOCIATION";
        }
        if ("COLLECTION_TO_ARRAY".equals(operation)) {
            return "COLLECTION_ELEMENT_REFERENCE_IDENTITY";
        }
        return "";
    }

    private String semanticContainerProjectionOperation(MethodSig method) {
        if (method == null) {
            return "";
        }
        if (javaMapContractOwner(method.owner)
                && method.params.isEmpty()) {
            if ("values".equals(method.name)
                    && "java.util.Collection".equals(
                    method.returnType)) {
                return "MAP_VALUES_VIEW";
            }
            if ("keySet".equals(method.name)
                    && "java.util.Set".equals(method.returnType)) {
                return "MAP_KEY_SET_VIEW";
            }
            if ("entrySet".equals(method.name)
                    && "java.util.Set".equals(method.returnType)) {
                return "MAP_ENTRY_SET_VIEW";
            }
        }
        if (javaCollectionContractOwner(method.owner)
                && "toArray".equals(method.name)
                && method.returnType.endsWith("[]")
                && (method.params.isEmpty()
                || (method.params.size() == 1
                && method.params.get(0).endsWith("[]")))) {
            return "COLLECTION_TO_ARRAY";
        }
        return "";
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
    private boolean processSemanticMapLookup(String callerMethod, Fact fact,
                                             MethodSig callee,
                                             List<String> defs,
                                             Set<String> callerRelevant) {
        if (!isSemanticMapLookup(callee) || defs.isEmpty()
                || !intersects(callerRelevant, defs)) {
            return false;
        }
        boolean changed = false;
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver != null) {
            String receiverNode = canonical(callerMethod, receiver);
            if (!ignoreNode(receiverNode)) {
                for (String def : defs) {
                    if (ignoreNode(def)) {
                        continue;
                    }
                    changed |= addEdge("map_lookup_state", receiverNode, def,
                            callerMethod, fact,
                            "Map.get result depends on receiver map contents");
                }
                changed |= callerRelevant.add(receiverNode);
            }
        }
        for (String actual : canonicalPositionList(callerMethod,
                actualInvokeArgs(fact.unitText))) {
            if (ignoreNode(actual)) {
                continue;
            }
            for (String def : defs) {
                if (ignoreNode(def)) {
                    continue;
                }
                changed |= addEdge("map_lookup_key", actual, def,
                        callerMethod, fact,
                        "Map.get result depends on lookup key");
            }
            changed |= callerRelevant.add(actual);
        }
        return changed;
    }

    private boolean isSemanticMapLookup(MethodSig callee) {
        if (callee == null || !"get".equals(callee.name)
                || callee.params.size() != 1) {
            return false;
        }
        return callee.owner.startsWith("java.util.")
                && (callee.owner.contains("Map")
                || "java.util.Hashtable".equals(callee.owner));
    }

    private boolean processConstructorObjectInvoke(String callerMethod, Fact fact,
                                                   MethodSig callee,
                                                   List<String> actuals,
                                                   Set<String> callerRelevant) {
        if (!"<init>".equals(callee.name)) {
            return false;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) {
            return false;
        }
        String callerReceiver = canonical(callerMethod, receiver);
        boolean exactReceiverDemand = callerRelevant.contains(callerReceiver);
        boolean projectedReceiverDemand = containsProjection(callerRelevant,
                callerReceiver);
        if (!exactReceiverDemand && !projectedReceiverDemand) {
            return false;
        }
        boolean changed = projectedReceiverDemand
                && processConstructorLeafFieldInitializers(callerMethod,
                fact, callee, actuals, callerReceiver, callerRelevant);
        if (!exactReceiverDemand) {
            return changed;
        }
        for (String actual : actuals) {
            if (ignoreNode(actual)) {
                continue;
            }
            if (addEdge("constructor_argument_object", actual, callerReceiver,
                    callerMethod, fact,
                    "constructor actual contributes to initialized receiver object")) {
                changed = true;
            }
            changed |= callerRelevant.add(actual);
        }
        return changed;
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
    private boolean processConstructorLeafFieldInitializers(
            String callerMethod, Fact fact, MethodSig constructor,
            List<String> actuals, String callerReceiver,
            Set<String> callerRelevant) {
        Set<String> suffixes = projectionSuffixesForBase(callerMethod,
                callerReceiver);
        if (suffixes.isEmpty()) {
            return false;
        }
        Map<String, Set<Integer>> parametersByField =
                constructorParametersByInitializedField(constructor.raw);
        if (parametersByField.isEmpty()) {
            return false;
        }

        boolean changed = false;
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
            if (addEdge("constructor_field_initialization", source, target,
                    callerMethod, fact,
                    "Soot-proven constructor parameter initializes demanded scalar leaf field")) {
                changed = true;
            }
            Map<String, Object> edge = emittedEdgeRows.get(edgeKey(
                    "constructor_field_initialization", source, target,
                    callerMethod, fact));
            if (edge != null) {
                edge.put("constructorMethod", constructor.raw);
                edge.put("constructorParameterIndex", parameter);
                edge.put("initializedField", fields.get(0));
                edge.put("projectedLeafPath", suffix);
                edge.put("leafOwnerPath", remaining);
                edge.put("constructorBindingAuthority",
                        "SOOT_PARAMETER_TO_THIS_FIELD_ASSIGNMENT_V1");
                edge.put("objectReferenceIsSymbolicScalar", false);
            }
            changed |= callerRelevant.add(source);
        }
        return changed;
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

    private boolean processReceiverSideEffectInvoke(String callerMethod, Fact fact,
                                                    MethodSig callee,
                                                    Set<String> callerRelevant,
                                                    Set<String> calleeRelevant) {
        if ("<init>".equals(callee.name)) {
            return false;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        if (receiver == null) {
            return false;
        }
        String callerReceiver = canonical(callerMethod, receiver);
        Set<String> suffixes = projectionSuffixesForBase(callerMethod, callerReceiver);
        if (suffixes.isEmpty()) {
            return false;
        }
        String calleeThis = methodThisNode(callee.raw);
        if (calleeThis == null) {
            return false;
        }
        boolean changed = false;
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
            if (addEdge("method_receiver_field_effect", calleeProjection,
                    callerProjection, callerMethod, fact,
                    "instance method may write receiver field observed by caller")) {
                changed = true;
            }
            changed |= calleeRelevant.add(calleeProjection);
            changed |= selectedMethods.add(callee.raw);
        }
        return changed;
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

    private boolean processAccessorInvoke(String callerMethod, Fact fact,
                                          MethodSig callee, List<String> defs,
                                          Set<String> callerRelevant) {
        if (callee == null || !callee.params.isEmpty() || defs.isEmpty()) {
            return false;
        }
        String receiver = invokeBaseLocal(fact.unitText);
        String fieldName = accessorFieldName(callee.name);
        if (receiver == null || fieldName.isEmpty()) {
            return false;
        }
        String receiverNode = canonical(callerMethod, receiver);
        String receiverField = fieldProjection(receiverNode, fieldName);
        if (ignoreNode(receiverField)) {
            return false;
        }
        SootField declaredField = resolveDeclaredField(callee.owner,
                fieldName);
        SootMethod declaredAccessor = resolveDeclaredAccessor(callee);
        String projectedType = declaredField == null
                ? cellValueType(receiverField)
                : declaredField.getType().toString();
        if (projectedType.isEmpty()
                || !erasedTypeName(projectedType).equals(
                erasedTypeName(callee.returnType))) {
            return false;
        }
        boolean changed = false;
        boolean defExactHit = exactIntersects(callerRelevant, defs);
        boolean defProjectionHit = projectionIntersects(callerRelevant, defs);
        boolean defHit = defExactHit || defProjectionHit;
        if (!defHit) {
            return false;
        }
        for (String def : defs) {
            if (ignoreNode(def)) {
                continue;
            }
            if (declaredField != null) {
                String declaredFieldNode = declaredField.getSignature();
                if (addEdge("accessor_field_return", declaredFieldNode,
                        def, callerMethod, fact,
                        "accessor return reads canonical declared field")) {
                    changed = true;
                }
                annotateAccessorDeclaredFieldEdge(declaredFieldNode, def,
                        callerMethod, fact, declaredField,
                        declaredAccessor);
            }
            if (addEdge("accessor_field_return", receiverField, def,
                    callerMethod, fact,
                    "accessor return reads receiver-local field projection")) {
                changed = true;
            }
            if (declaredField != null) {
                annotateAccessorDeclaredFieldEdge(receiverField, def,
                        callerMethod, fact, declaredField,
                        declaredAccessor);
            }
        }
        if (defExactHit && canOpenFieldFromPlainValues(defs)) {
            changed |= callerRelevant.add(receiverField);
            if (declaredField != null) {
                changed |= callerRelevant.add(
                        declaredField.getSignature());
            }
        }
        if (defProjectionHit) {
            changed |= callerRelevant.add(receiverField);
            if (declaredField != null) {
                changed |= callerRelevant.add(
                        declaredField.getSignature());
            }
        }
        return changed;
    }

    private void annotateAccessorDeclaredFieldEdge(
            String from, String to, String method, Fact fact,
            SootField field, SootMethod accessor) {
        Map<String, Object> edge = emittedEdgeRows.get(edgeKey(
                "accessor_field_return", from, to, method, fact));
        if (edge == null || field == null) {
            return;
        }
        edge.put("declaredFieldSignature", field.getSignature());
        edge.put("declaredFieldOwner",
                field.getDeclaringClass().getName());
        edge.put("declaredFieldType", field.getType().toString());
        edge.put("declaredFieldName", field.getName());
        edge.put("declaredFieldAuthority",
                "SOOT_RESOLVED_DECLARATION_HIERARCHY");
        if (accessor != null) {
            edge.put("accessorImplementationMethod",
                    accessor.getSignature());
            edge.put("accessorImplementationAuthority",
                    "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
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
        Map<String, Object> edge = emittedEdgeRows.get(edgeKey(kind,
                from, to, method, fact));
        String owner = fieldOwner(fieldSignature);
        String name = fieldNameFromSignature(fieldSignature);
        SootField field = resolveDeclaredField(owner, name);
        if (edge == null || field == null
                || !field.getSignature().equals(fieldSignature)) {
            return;
        }
        edge.put("declaredFieldSignature", field.getSignature());
        edge.put("declaredFieldOwner",
                field.getDeclaringClass().getName());
        edge.put("declaredFieldType", field.getType().toString());
        edge.put("declaredFieldName", field.getName());
        edge.put("declaredFieldAuthority",
                "SOOT_RESOLVED_DECLARATION_HIERARCHY");
    }

    /** Resolves the concrete declaration inherited by an accessor owner. */
    private SootMethod resolveDeclaredAccessor(MethodSig accessor) {
        if (accessor == null || accessor.owner.isEmpty()) {
            return null;
        }
        SootClass root = classesByName.get(accessor.owner);
        if (root == null) {
            try {
                root = Scene.v().getSootClassUnsafe(accessor.owner);
            } catch (RuntimeException ignored) {
                return null;
            }
        }
        if (root == null) {
            return null;
        }
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
                for (SootMethod method : sootClass.getMethods()) {
                    if (!accessor.name.equals(method.getName())
                            || !erasedTypeName(accessor.returnType).equals(
                            erasedTypeName(method.getReturnType()
                                    .toString()))
                            || method.getParameterCount()
                            != accessor.params.size()) {
                        continue;
                    }
                    boolean parametersMatch = true;
                    for (int index = 0; index < accessor.params.size();
                         index++) {
                        if (!erasedTypeName(accessor.params.get(index))
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
                if (sootClass.hasSuperclass()) {
                    work.addFirst(sootClass.getSuperclass());
                }
                for (SootClass iface : sootClass.getInterfaces()) {
                    work.addLast(iface);
                }
            } catch (RuntimeException exception) {
                return null;
            }
        }
        return null;
    }

    private boolean processRpcInvoke(String callerMethod, Fact fact, MethodSig callee,
                                     List<String> defs, List<String> actuals,
                                     Set<String> callerRelevant) {
        List<RpcTarget> targets = resolveRpcTargets(callerMethod, callee);
        if (targets.isEmpty()) {
            return false;
        }
        boolean changed = false;
        int count = 0;
        for (RpcTarget target : targets) {
            if (target.targetSignature.equals(callee.raw)) {
                continue;
            }
            if (count++ >= MAX_RPC_TARGETS_PER_CALL) {
                break;
            }
            SootMethod targetMethod = methodsBySignature.get(target.targetSignature);
            if (targetMethod == null) {
                continue;
            }
            if (selectedMethods.size() < maxMethods) {
                loadMethod(targetMethod);
            }
            MethodSig targetSig = parseMethodSig(target.targetSignature);
            if (targetSig == null) {
                continue;
            }
            Set<String> targetRelevant = relevant(target.targetSignature);
            int paramCount = Math.min(actuals.size(), targetSig.params.size());
            for (int i = 0; i < paramCount; i++) {
                String actual = actuals.get(i);
                if (ignoreNode(actual)) {
                    continue;
                }
                String formal = formalParam(targetSig, i);
                boolean formalExactHit = targetRelevant.contains(formal);
                boolean formalProjectionHit = containsProjection(targetRelevant, formal);
                boolean formalHit = formalExactHit || formalProjectionHit;
                boolean actualExactHit = callerRelevant.contains(actual);
                boolean actualProjectionHit = containsProjection(callerRelevant, actual);
                boolean actualHit = actualExactHit || actualProjectionHit;
                if (formalHit || actualHit) {
                    if (addEdge("rpc_argument", actual, formal, callerMethod, fact,
                            "RPC actual flows to discovered server-side formal")) {
                        changed = true;
                    }
                    if (formalExactHit) {
                        changed |= callerRelevant.add(actual);
                    }
                    if (actualHit) {
                        changed |= targetRelevant.add(formal);
                        changed |= selectedMethods.add(target.targetSignature);
                    }
                }
            }
            for (String def : defs) {
                String returnNode = target.targetSignature + ".return";
                boolean defExactHit = callerRelevant.contains(def);
                boolean defProjectionHit = containsProjection(callerRelevant, def);
                boolean defHit = defExactHit || defProjectionHit;
                if (defHit) {
                    if (addEdge("rpc_return", returnNode, def, callerMethod, fact,
                            "discovered server-side RPC return flows to caller")) {
                        changed = true;
                    }
                if (defExactHit || defProjectionHit) {
                    changed |= targetRelevant.add(returnNode);
                    changed |= selectedMethods.add(target.targetSignature);
                }
                }
            }
        }
        return changed;
    }

    private List<RpcTarget> resolveRpcTargets(String callerMethod, MethodSig callee) {
        List<RpcTarget> targets = rpcTargetsBySource.get(callee.raw);
        if (targets == null || targets.isEmpty()) {
            return Collections.emptyList();
        }
        String callerOwner = ownerOf(callerMethod);
        if (isHdfsKeyPropagationFastPathTarget()
                && "org.apache.hadoop.hdfs.server.protocol.NamenodeProtocol"
                .equals(callee.owner)
                && "getBlockKeys".equals(callee.name)
                && !callerOwner.contains("ServerSideTranslatorPB")) {
            return targets;
        }
        List<RpcTarget> preferred = new ArrayList<>();
        for (RpcTarget target : targets) {
            String owner = ownerOf(target.targetSignature);
            if (callerOwner.contains("ServerSideTranslatorPB")) {
                if (!owner.contains("TranslatorPB")
                        && (owner.contains("RpcServer") || owner.contains(".server.")
                        || owner.endsWith("DataNode"))) {
                    preferred.add(target);
                }
            } else if (callee.owner.endsWith("PB")
                    || callee.owner.contains("protocolPB")) {
                if (owner.contains("ServerSideTranslatorPB")) {
                    preferred.add(target);
                }
            } else if (!callerOwner.contains("ServerSideTranslatorPB")) {
                if (owner.contains("TranslatorPB")
                        && !owner.contains("ServerSideTranslatorPB")) {
                    preferred.add(target);
                }
            }
        }
        return preferred.isEmpty() ? targets : preferred;
    }

    private boolean processDispatchInvoke(String callerMethod, Fact fact,
                                          MethodSig callee, List<String> defs,
                                          List<String> actuals,
                                          Set<String> callerRelevant) {
        List<String> targetMethods = resolveDispatchTargets(callee);
        if (targetMethods.isEmpty()) {
            return false;
        }
        RuntimeDispatchSelection runtimeSelection =
                runtimeDispatchSelection(callerMethod, fact, callee,
                        targetMethods);
        if (runtimeSelection.blocked()) {
            blockRuntimeDispatch(runtimeSelection);
            return false;
        }
        if (runtimeSelection.unique()) {
            targetMethods = runtimeSelection.targets;
            runtimeSelectedDispatchSites.add(runtimeSelection.siteId);
        } else {
            targetMethods = callbackBoundDispatchTargets(callerMethod,
                    callee, targetMethods);
            targetMethods = CausynthPipeline.conservativeDispatchTargets(
                    targetMethods);
        }
        if (!runtimeSelection.unique()
                && targetMethods.size()
                > MAX_DISPATCH_TARGETS_PER_CALL) {
            blockRuntimeDispatch(runtimeSelection.withReason(
                    "STATIC_DISPATCH_TARGET_LIMIT_EXCEEDED:"
                            + targetMethods.size()));
            return false;
        }
        boolean changed = false;
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
                if (!admitRuntimeRecursiveMethod(targetMethod,
                        runtimeSelection.siteId)) {
                    blockRuntimeDispatch(runtimeSelection.withReason(
                            "RUNTIME_RECURSIVE_METHOD_LIMIT_EXCEEDED"));
                    continue;
                }
            } else if (selectedMethods.size() < maxMethods) {
                loadMethod(sootMethod);
            }
            MethodSig targetSig = parseMethodSig(targetMethod);
            if (targetSig == null) {
                continue;
            }
            int edgeStart = edges.size();
            Set<String> targetRelevant = relevant(targetMethod);
            boolean runtimeReturnExpansion = runtimeSelection.unique()
                    && !callerRelevant.isEmpty()
                    && !defs.isEmpty()
                    && canCarryProjectedFieldContainer(
                            targetSig.returnType);
            boolean callRelevant = intersects(callerRelevant, defs)
                    || runtimeReturnExpansion;
            int paramCount = Math.min(actuals.size(), targetSig.params.size());
            for (int i = 0; i < paramCount; i++) {
                String actual = actuals.get(i);
                if (ignoreNode(actual)) {
                    continue;
                }
                String formal = formalParam(targetSig, i);
                boolean formalExactHit = targetRelevant.contains(formal);
                boolean formalProjectionHit = containsProjection(targetRelevant, formal);
                boolean formalHit = formalExactHit || formalProjectionHit;
                boolean actualExactHit = callerRelevant.contains(actual);
                boolean actualProjectionHit = containsProjection(callerRelevant, actual);
                boolean actualHit = actualExactHit || actualProjectionHit;
                if (formalHit || actualHit) {
                    callRelevant = true;
                    if (addEdge("dispatch_argument", actual, formal,
                            callerMethod, fact,
                            "interface/virtual dispatch actual flows to concrete formal")) {
                        changed = true;
                    }
                    if (formalExactHit) {
                        changed |= callerRelevant.add(actual);
                    }
                    if (actualHit) {
                        changed |= targetRelevant.add(formal);
                        changed |= selectedMethods.add(targetMethod);
                    }
                }
            }
            for (String def : defs) {
                String returnNode = targetMethod + ".return";
                boolean defExactHit = callerRelevant.contains(def);
                boolean defProjectionHit = containsProjection(callerRelevant, def);
                boolean defHit = defExactHit || defProjectionHit
                        || runtimeReturnExpansion;
                if (defHit) {
                    if (addEdge("dispatch_return", returnNode, def,
                            callerMethod, fact,
                            "concrete dispatch return flows to caller")) {
                        changed = true;
                    }
                    if (defExactHit || defProjectionHit) {
                        changed |= targetRelevant.add(returnNode);
                        changed |= selectedMethods.add(targetMethod);
                    }
                    if (runtimeReturnExpansion) {
                        changed |= callerRelevant.add(def);
                        changed |= targetRelevant.add(returnNode);
                        changed |= selectedMethods.add(targetMethod);
                    }
                }
            }
            String callerReceiver = canonical(callerMethod,
                    invokeBaseLocal(fact.unitText));
            String targetThis = methodThisNode(targetMethod);
            if (callRelevant && targetThis != null
                    && !ignoreNode(callerReceiver)) {
                if (addEdge("dispatch_receiver", callerReceiver, targetThis,
                        callerMethod, fact,
                        "runtime receiver selects and aliases concrete dispatch target")) {
                    changed = true;
                }
                changed |= callerRelevant.add(callerReceiver);
                changed |= targetRelevant.add(targetThis);
                changed |= selectedMethods.add(targetMethod);
            }
            if (runtimeSelection.unique()) {
                annotateRuntimeDispatchEdges(edgeStart, callerMethod,
                        fact, runtimeSelection, runtimeReturnExpansion);
            }
        }
        return changed;
    }

    /**
     * Resolves an interface callback using the concrete object captured at
     * its registration site.  Class-hierarchy dispatch alone sees both
     * encrypted and general-purpose PasswordFunction implementations in
     * the same handle() body.  Only the registration whose implementation
     * can reach the configured exception belongs to this backward slice.
     */
    private List<String> callbackBoundDispatchTargets(String callerMethod,
                                                      MethodSig callee,
                                                      List<String> targets) {
        if (callee == null
                || !callee.owner.equals(HDFS_SASL_SERVER
                + "$PasswordFunction")
                || !"apply".equals(callee.name)
                || !callerMethod.contains(HDFS_SASL_SERVER
                + "$SaslServerCallbackHandler: void handle(")) {
            return targets;
        }
        Set<String> bound = new LinkedHashSet<>();
        for (StaticPortMapping dataflow : staticPortMappings) {
            if ("synchronous_callback_capture_receiver".equals(dataflow.kind)
                    && reachesDiscoveredException(dataflow.activationMethod)) {
                bound.add(dataflow.activationMethod);
            }
        }
        if (bound.isEmpty()) {
            return targets;
        }
        List<String> filtered = new ArrayList<>();
        for (String target : targets) {
            if (bound.contains(target)) {
                filtered.add(target);
            }
        }
        return filtered.isEmpty() ? targets : filtered;
    }

    /**
     * Refines one class-hierarchy dispatch with exact runtime call-site
     * evidence.  Runtime evidence is optional.  When present, it is
     * authoritative only for the exact (caller, unit, declared callee)
     * triple; observations from another unit or caller are never reused.
     * Multiple actual callees at that exact site are deliberately
     * rejected instead of being conjoined as one symbolic definition.
     */
    private RuntimeDispatchSelection runtimeDispatchSelection(
            String callerMethod, Fact fact, MethodSig callee,
            List<String> staticTargets) {
        String siteId = stableSiteId(callerMethod,
                fact == null ? -1 : fact.unitIndex, "dispatch");
        RuntimeDispatchObservation observation =
                runtimeDispatchEvidence.lookup(callerMethod, siteId,
                        callee == null ? "" : callee.raw);
        if (observation == null) {
            return RuntimeDispatchSelection.staticFallback(siteId,
                    staticTargets);
        }
        if (observation.actualCallees.size() != 1) {
            return RuntimeDispatchSelection.blocked(siteId,
                    observation.actualCallees,
                    "AMBIGUOUS_RUNTIME_ACTUAL_CALLEE");
        }
        String actual = observation.actualCallees.iterator().next();
        if (!staticTargets.contains(actual)) {
            return RuntimeDispatchSelection.blocked(siteId,
                    observation.actualCallees,
                    "RUNTIME_ACTUAL_CALLEE_OUTSIDE_STATIC_HIERARCHY");
        }
        return RuntimeDispatchSelection.runtimeUnique(siteId, actual,
                runtimeDispatchEvidence.source());
    }

    private void blockRuntimeDispatch(RuntimeDispatchSelection selection) {
        if (selection == null || !selection.blocked()) {
            return;
        }
        blockedRuntimeDispatchSites.put(selection.siteId,
                selection.reason + ":" + selection.actualCallees);
    }

    private boolean admitRuntimeRecursiveMethod(String method,
                                                 String siteId) {
        if (runtimeRecursiveMethods.contains(method)) {
            return true;
        }
        if (runtimeRecursiveMethods.size()
                >= MAX_RUNTIME_RECURSIVE_METHODS) {
            blockedRuntimeDispatchSites.put(siteId,
                    "RUNTIME_RECURSIVE_METHOD_LIMIT_EXCEEDED:" + method);
            return false;
        }
        SootMethod sootMethod = methodsBySignature.get(method);
        if (sootMethod == null || !sootMethod.isConcrete()) {
            blockedRuntimeDispatchSites.put(siteId,
                    "RUNTIME_ACTUAL_CALLEE_BODY_UNAVAILABLE:" + method);
            return false;
        }
        runtimeRecursiveMethods.add(method);
        selectedMethods.add(method);
        if (!factsByMethod.containsKey(method) && !loadMethod(sootMethod)) {
            blockedRuntimeDispatchSites.put(siteId,
                    "RUNTIME_ACTUAL_CALLEE_BODY_UNREADABLE:" + method);
            return false;
        }
        return true;
    }

    private void annotateRuntimeDispatchEdges(
            int edgeStart, String callerMethod, Fact fact,
            RuntimeDispatchSelection selection,
            boolean recursiveReturnExpansion) {
        String siteId = stableSiteId(callerMethod,
                fact == null ? -1 : fact.unitIndex, "dispatch");
        for (int index = Math.max(0, edgeStart);
             index < edges.size(); index++) {
            Map<String, Object> edge = edges.get(index);
            String kind = stringValue(edge.get("kind"));
            if (!kind.contains("dispatch")
                    || !callerMethod.equals(stringValue(
                    edge.get("method")))
                    || !siteId.equals(stringValue(edge.get("siteId")))) {
                continue;
            }
            edge.put("runtimeSelectedDispatch", true);
            edge.put("dispatchSelectionAuthority",
                    "UNIQUE_CALLSITE_CORRELATED_ACTUAL_CALLEE_V1");
            edge.put("runtimeCallEdgeSource", selection.source);
            edge.put("runtimeCallSiteId", selection.siteId);
            edge.put("runtimeActualCallee",
                    selection.targets.get(0));
            edge.put("runtimeEvidenceLevel", "CALLSITE_CORRELATED");
            edge.put("runtimeRecursiveReturnExpansion",
                    recursiveReturnExpansion);
        }
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

    private boolean expandCallers(String calleeMethod) {
        if (!isExpandableMethod(calleeMethod)) {
            return false;
        }
        List<Fact> callers = callersByCallee.get(calleeMethod);
        if (callers == null) {
            return false;
        }
        MethodSig callee = parseMethodSig(calleeMethod);
        if (callee == null) {
            return false;
        }
        Set<String> calleeRelevant = relevant(calleeMethod);
        String returnNode = callee.raw + ".return";
        boolean returnRelevant = calleeRelevant.contains(returnNode)
                || containsProjection(calleeRelevant, returnNode);
        boolean changed = false;
        for (Fact caller : callers) {
            if (selectedMethods.size() >= maxMethods) {
                break;
            }
            Set<String> callerRelevant = relevant(caller.method);
            List<String> actuals = canonicalPositionList(caller.method,
                    actualInvokeArgs(caller.unitText));
            for (int i = 0; i < actuals.size() && i < callee.params.size(); i++) {
                String formal = formalParam(callee, i);
                if (!calleeRelevant.contains(formal)
                        && !containsProjection(calleeRelevant, formal)) {
                    continue;
                }
                String actual = actuals.get(i);
                if (ignoreNode(actual)) {
                    continue;
                }
                if (addEdge("caller_argument", actual, formal, caller.method, caller,
                        "caller actual reaches relevant callee formal")) {
                    changed = true;
                }
                changed |= callerRelevant.add(actual);
                changed |= selectedMethods.add(caller.method);
            }
            if (returnRelevant) {
                List<String> defs = canonicalList(caller.method, caller.defs);
                changed |= expandCallerReturn("caller_return", returnNode,
                        defs, caller.method, caller, callerRelevant,
                        "caller receives relevant callee return");
            }
        }
        return changed;
    }

    private boolean expandRpcCallers(String targetMethod) {
        List<RpcTarget> sources = rpcSourcesByTarget.get(targetMethod);
        if (sources == null || sources.isEmpty()) {
            return false;
        }
        MethodSig targetSig = parseMethodSig(targetMethod);
        if (targetSig == null) {
            return false;
        }
        Set<String> targetRelevant = relevant(targetMethod);
        String returnNode = targetMethod + ".return";
        boolean returnRelevant = targetRelevant.contains(returnNode)
                || containsProjection(targetRelevant, returnNode);
        boolean changed = false;
        buildGlobalStaticIndex();
        for (RpcTarget source : sources) {
            List<MethodCallsite> callsites = methodCallersByCallee
                    .get(source.sourceSignature);
            if (callsites == null) {
                continue;
            }
            for (MethodCallsite callsite : callsites) {
                if (selectedMethods.size() >= maxMethods) {
                    break;
                }
                SootMethod callerMethod = methodsBySignature.get(callsite.method);
                if (callerMethod != null && loadMethod(callerMethod)) {
                    changed = true;
                }
                Set<String> callerRelevant = relevant(callsite.method);
                List<String> actuals = callsite.actuals;
                int paramCount = Math.min(actuals.size(), targetSig.params.size());
                for (int i = 0; i < paramCount; i++) {
                    String formal = formalParam(targetSig, i);
                    if (!targetRelevant.contains(formal)
                            && !containsProjection(targetRelevant, formal)) {
                        continue;
                    }
                    String actual = actuals.get(i);
                    if (ignoreNode(actual)) {
                        continue;
                    }
                    if (addEdge("rpc_caller_argument", actual, formal,
                            callsite.method, callsite.fact,
                            "RPC caller actual reaches discovered server-side formal")) {
                        changed = true;
                    }
                    changed |= callerRelevant.add(actual);
                    changed |= selectedMethods.add(callsite.method);
                }
                if (returnRelevant) {
                    changed |= expandCallerReturn("rpc_caller_return",
                            returnNode, callsite.defs, callsite.method,
                            callsite.fact, callerRelevant,
                            "RPC caller receives relevant server-side return");
                }
            }
        }
        return changed;
    }

    private boolean expandDispatchCallers(String targetMethod) {
        List<String> sourceMethods = resolveDispatchSources(targetMethod);
        if (sourceMethods.isEmpty()) {
            return false;
        }
        MethodSig targetSig = parseMethodSig(targetMethod);
        if (targetSig == null) {
            return false;
        }
        Set<String> targetRelevant = relevant(targetMethod);
        String returnNode = targetMethod + ".return";
        boolean returnRelevant = targetRelevant.contains(returnNode)
                || containsProjection(targetRelevant, returnNode);
        String targetThis = methodThisNode(targetMethod);
        Set<String> targetThisProjectionSuffixes =
                projectionSuffixesForBase(targetMethod, targetThis);
        boolean targetThisRelevant = targetThis != null
                && (targetRelevant.contains(targetThis)
                || !targetThisProjectionSuffixes.isEmpty());
        boolean changed = false;
        buildGlobalStaticIndex();
        for (String sourceMethod : sourceMethods) {
            List<MethodCallsite> callsites = methodCallersByCallee.get(sourceMethod);
            if (callsites == null) {
                continue;
            }
            for (MethodCallsite callsite : callsites) {
                if (selectedMethods.size() >= maxMethods
                        && !runtimeRecursiveMethods.contains(
                        targetMethod)) {
                    break;
                }
                MethodSig sourceSig = parseMethodSig(sourceMethod);
                RuntimeDispatchSelection runtimeSelection =
                        runtimeDispatchSelection(callsite.method,
                                callsite.fact, sourceSig,
                                resolveDispatchTargets(sourceSig));
                if (runtimeSelection.blocked()) {
                    blockRuntimeDispatch(runtimeSelection);
                    continue;
                }
                if (runtimeSelection.unique()
                        && !runtimeSelection.targets.contains(
                        targetMethod)) {
                    continue;
                }
                if (!runtimeSelection.unique()
                        && !callbackDispatchTargetAllowed(callsite.method,
                        targetMethod)) {
                    continue;
                }
                if (runtimeSelection.unique()) {
                    runtimeSelectedDispatchSites.add(
                            runtimeSelection.siteId);
                    if (!admitRuntimeRecursiveMethod(targetMethod,
                            runtimeSelection.siteId)) {
                        continue;
                    }
                }
                int edgeStart = edges.size();
                SootMethod callerMethod = methodsBySignature.get(callsite.method);
                if (callerMethod != null && loadMethod(callerMethod)) {
                    changed = true;
                }
                Set<String> callerRelevant = relevant(callsite.method);
                List<String> actuals = callsite.actuals;
                int paramCount = Math.min(actuals.size(), targetSig.params.size());
                for (int i = 0; i < paramCount; i++) {
                    String formal = formalParam(targetSig, i);
                    if (!targetRelevant.contains(formal)
                            && !containsProjection(targetRelevant, formal)) {
                        continue;
                    }
                    String actual = actuals.get(i);
                    if (ignoreNode(actual)) {
                        continue;
                    }
                    if (addEdge("dispatch_caller_argument", actual, formal,
                            callsite.method, callsite.fact,
                            "interface/virtual caller actual reaches concrete formal")) {
                        changed = true;
                    }
                    changed |= callerRelevant.add(actual);
                    changed |= selectedMethods.add(callsite.method);
                }
                if (returnRelevant) {
                    changed |= expandCallerReturn("dispatch_caller_return",
                            returnNode, callsite.defs, callsite.method,
                            callsite.fact, callerRelevant,
                            "interface/virtual caller receives relevant concrete return");
                }
                if (targetThisRelevant) {
                    changed |= expandDispatchReceiverFields(targetMethod,
                            targetThis, targetThisProjectionSuffixes,
                            callsite);
                }
                if (runtimeSelection.unique()) {
                    annotateRuntimeDispatchEdges(edgeStart,
                            callsite.method, callsite.fact,
                            runtimeSelection, false);
                }
            }
        }
        return changed;
    }

    private boolean expandCallerReturn(String kind, String returnNode,
                                       List<String> defs, String callerMethod,
                                       Fact fact, Set<String> callerRelevant,
                                       String evidence) {
        if (defs == null || defs.isEmpty() || ignoreNode(returnNode)) {
            return false;
        }
        boolean changed = false;
        for (String def : defs) {
            if (ignoreNode(def)) {
                continue;
            }
            if (addEdge(kind, returnNode, def, callerMethod, fact, evidence)) {
                changed = true;
            }
            changed |= callerRelevant.add(def);
            changed |= selectedMethods.add(callerMethod);
        }
        return changed;
    }

    private boolean expandDispatchReceiverFields(String targetMethod,
                                                 String targetThis,
                                                 Set<String> suffixes,
                                                 MethodCallsite callsite) {
        if (targetThis == null || callsite == null
                || ignoreNode(callsite.receiver)) {
            return false;
        }
        boolean changed = false;
        if (relevant(targetMethod).contains(targetThis)) {
            if (addEdge("dispatch_caller_receiver", callsite.receiver,
                    targetThis, callsite.method, callsite.fact,
                    "interface/virtual receiver aliases concrete this")) {
                changed = true;
            }
            changed |= relevant(callsite.method).add(callsite.receiver);
            changed |= selectedMethods.add(callsite.method);
        }
        for (String suffix : suffixes) {
            if (!isAllowedFieldPathSuffix(suffix)) {
                continue;
            }
            String callerProjection = callsite.receiver + suffix;
            String targetProjection = targetThis + suffix;
            if (addEdge("dispatch_caller_receiver_field", callerProjection,
                    targetProjection, callsite.method, callsite.fact,
                    "interface/virtual receiver field aliases concrete this field")) {
                changed = true;
            }
            changed |= relevant(callsite.method).add(callerProjection);
            changed |= selectedMethods.add(callsite.method);
        }
        return changed;
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

    private boolean callbackDispatchTargetAllowed(String callerMethod,
                                                  String targetMethod) {
        if (callerMethod == null || targetMethod == null
                || !callerMethod.contains(HDFS_SASL_SERVER
                + "$SaslServerCallbackHandler: void handle(")
                || !targetMethod.contains(HDFS_SASL_SERVER + "$")) {
            return true;
        }
        for (StaticPortMapping dataflow : staticPortMappings) {
            if ("synchronous_callback_capture_receiver".equals(dataflow.kind)
                    && targetMethod.equals(dataflow.activationMethod)) {
                return reachesDiscoveredException(targetMethod);
            }
        }
        return true;
    }

    private boolean expandStaticPortMappings(String method) {
        if (staticPortMappings.isEmpty()) {
            return false;
        }
        boolean changed = false;
        Set<String> methodRelevant = relevant(method);
        for (StaticPortMapping dataflow : staticPortMappings) {
            if (!staticPortMappingActive(dataflow)) {
                continue;
            }
            if (dataflow.targetMethod.equals(method)
                    && relevantContainsProjectionOrExact(methodRelevant,
                    dataflow.targetCell)) {
                if (loadMethod(methodsBySignature.get(dataflow.sourceMethod))) {
                    changed = true;
                }
                Set<String> sourceRelevant = relevant(dataflow.sourceMethod);
                if (addEdge(dataflow.kind, dataflow.sourceCell, dataflow.targetCell,
                        dataflow.edgeMethod, null, dataflow.evidence)) {
                    changed = true;
                }
                changed |= sourceRelevant.add(dataflow.sourceCell);
                changed |= selectedMethods.add(dataflow.sourceMethod);
                changed |= addStaticPortMappingPathGuards(dataflow);
            }
            if (dataflow.sourceMethod.equals(method)
                    && relevantContainsProjectionOrExact(methodRelevant,
                    dataflow.sourceCell)) {
                if (loadMethod(methodsBySignature.get(dataflow.targetMethod))) {
                    changed = true;
                }
                Set<String> targetRelevant = relevant(dataflow.targetMethod);
                if (addEdge(dataflow.kind, dataflow.sourceCell, dataflow.targetCell,
                        dataflow.edgeMethod, null, dataflow.evidence)) {
                    changed = true;
                }
                changed |= targetRelevant.add(dataflow.targetCell);
                changed |= selectedMethods.add(dataflow.targetMethod);
                changed |= addStaticPortMappingPathGuards(dataflow);
            }
        }
        return changed;
    }

    private boolean staticPortMappingActive(StaticPortMapping dataflow) {
        if (dataflow.activationMethod == null
                || dataflow.activationMethod.isEmpty()) {
            return true;
        }
        Set<String> demand = relevantByMethod.get(dataflow.activationMethod);
        String returnNode = dataflow.activationMethod + ".return";
        return (!dataflow.kind.startsWith("synchronous_callback")
                || reachesDiscoveredException(dataflow.activationMethod))
                && selectedMethods.contains(dataflow.activationMethod)
                && demand != null
                && (demand.contains(returnNode)
                || containsProjection(demand, returnNode));
    }

    private boolean reachesDiscoveredException(String sourceMethod) {
        if (discoveredExceptionMethods.isEmpty()) {
            return true;
        }
        Boolean cached = exceptionReachabilityCache.get(sourceMethod);
        if (cached != null) {
            return cached;
        }
        Set<String> seen = new LinkedHashSet<>();
        Deque<String> queue = new ArrayDeque<>();
        seen.add(sourceMethod);
        queue.add(sourceMethod);
        while (!queue.isEmpty() && seen.size() < 256) {
            String method = queue.removeFirst();
            if (discoveredExceptionMethods.contains(method)) {
                exceptionReachabilityCache.put(sourceMethod, true);
                return true;
            }
            SootMethod sootMethod = methodsBySignature.get(method);
            if (sootMethod == null) {
                continue;
            }
            for (Fact fact : factsFromMethod(sootMethod)) {
                MethodSig invoked = parseMethodSig(fact.invoke);
                if (invoked == null
                        || !methodsBySignature.containsKey(invoked.raw)
                        || !isApplicationClassName(invoked.owner)
                        || !seen.add(invoked.raw)) {
                    continue;
                }
                queue.addLast(invoked.raw);
            }
        }
        exceptionReachabilityCache.put(sourceMethod, false);
        return false;
    }

    private boolean addStaticPortMappingPathGuards(
            StaticPortMapping dataflow) {
        if (dataflow.pathSite == null || dataflow.pathCell == null
                || dataflow.pathCell.isEmpty()) {
            return false;
        }
        SootMethod pathMethod = methodsBySignature.get(dataflow.pathSite.method);
        boolean changed = loadMethod(pathMethod);
        Set<String> pathRelevant = relevant(dataflow.pathSite.method);
        changed |= selectedMethods.add(dataflow.pathSite.method);
        for (ExceptionGuard guard : controllingGuards(
                dataflow.pathSite.method, dataflow.pathSite)) {
            for (String use : causalGuardUses(guard.fact)) {
                String guardNode = canonical(dataflow.pathSite.method, use);
                if (ignoreNode(guardNode)) {
                    continue;
                }
                String kind = "synchronous_callback_path_guard";
                changed |= addEdge(kind,
                        guardNode, dataflow.targetCell,
                        dataflow.pathSite.method, guard.fact,
                        "synchronous callback invocation requires Jimple outcome "
                                + guard.requiredOutcome + " at callback site u"
                                + dataflow.pathSite.unitIndex);
                Map<String, Object> edge = emittedEdgeRows.get(edgeKey(
                        kind, guardNode, dataflow.targetCell,
                        dataflow.pathSite.method, guard.fact));
                if (edge != null) {
                    ControlDependenceEdgeSupport.annotatePathGuard(
                            edge, dataflow.pathSite.method,
                            guard.fact.unitIndex,
                            dataflow.pathSite.unitIndex,
                            dataflow.pathSite.unitText,
                            guard.requiredOutcome,
                            guard.reachingSuccessorIndices,
                            guardNode, dataflow.targetCell);
                    guard.branchShape.annotate(edge);
                }
                changed |= pathRelevant.add(guardNode);
            }
        }
        return changed;
    }

    private boolean propagateProjectedEdgesFromExistingEdges() {
        if (edges.isEmpty() || edges.size() >= maxEdges) {
            return false;
        }
        boolean changed = false;
        List<Map<String, Object>> snapshot = new ArrayList<>(edges);
        for (Map<String, Object> edge : snapshot) {
            if (edges.size() >= maxEdges) {
                break;
            }
            String kind = String.valueOf(edge.get("kind"));
            String from = String.valueOf(edge.get("fromCell"));
            String to = String.valueOf(edge.get("toCell"));
            String method = String.valueOf(edge.get("method"));
            projectedPassEdgeChecks++;
            boolean edgeHasInvoke = edge.get("invoke") != null;
            if (!supportsProjectedPropagation(kind)
                    || ("local_def_use".equals(kind) && edgeHasInvoke)
                    || !canCarryProjectedFields(from)
                    || !canCarryProjectedFields(to)) {
                projectedPassUnsupported++;
                continue;
            }
            Set<String> suffixes = new LinkedHashSet<>();
            suffixes.addAll(projectionSuffixesForBase(method, from));
            suffixes.addAll(projectionSuffixesForBase(method, to));
            if (suffixes.isEmpty()) {
                projectedPassNoSuffix++;
                continue;
            }
            projectedPassCandidates++;
            if (addProjectedEdgesForObjectFlow(kind, from, to, method,
                    null, edge)) {
                projectedPassEmitted++;
                changed = true;
            }
        }
        return changed;
    }

    private boolean isExpandableMethod(String signature) {
        SootMethod method = methodsBySignature.get(signature);
        MethodSig sig = parseMethodSig(signature);
        return method != null
                && method.isConcrete()
                && method.getDeclaringClass().isApplicationClass()
                && !method.getDeclaringClass().isInterface()
                && !method.getDeclaringClass().isAbstract()
                && !isAccessor(sig);
    }

    private boolean isAccessor(MethodSig sig) {
        if (sig == null) {
            return false;
        }
        if (!sig.params.isEmpty()) {
            boolean requiredContainerLookup =
                    ("org.apache.hadoop.hdfs.security.token.block."
                            + "BlockPoolTokenSecretManager").equals(sig.owner)
                            && "get".equals(sig.name)
                            && sig.params.size() == 1;
            return "get".equals(sig.name) && !requiredContainerLookup;
        }
        boolean identifierOrKeyAccessor = (sig.owner.endsWith("Identifier")
                || sig.owner.endsWith("BlockKey")) && sig.name.startsWith("get");
        return identifierOrKeyAccessor
                || sig.name.startsWith("is")
                || "toString".equals(sig.name)
                || "hashCode".equals(sig.name);
    }

    private List<Map<String, Object>> collectCells() {
        Set<String> cells = new LinkedHashSet<>();
        cells.add(target.seedPredicate());
        for (Map<String, Object> edge : edges) {
            cells.add(String.valueOf(edge.get("fromCell")));
            cells.add(String.valueOf(edge.get("toCell")));
        }
        List<Map<String, Object>> output = new ArrayList<>();
        int index = 0;
        for (String cell : cells) {
            output.add(object(
                    "id", "C." + index++,
                    "cell", cell,
                    "kind", cellKind(cell)));
        }
        return output;
    }

    private Set<String> relevant(String method) {
        return relevantByMethod.computeIfAbsent(method, ignored -> new LinkedHashSet<>());
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

    private boolean expandMethodReceiverFields(String calleeMethod, String calleeThis,
                                               Set<String> suffixes,
                                               MethodCallsite callsite) {
        if (calleeThis == null || ignoreNode(callsite.receiver)) {
            return false;
        }
        boolean changed = false;
        if (relevant(calleeMethod).contains(calleeThis)) {
            if (addEdge("method_receiver", callsite.receiver, calleeThis,
                    callsite.method, callsite.fact,
                    "instance method receiver flows to callee this")) {
                changed = true;
            }
            changed |= relevant(callsite.method).add(callsite.receiver);
            changed |= selectedMethods.add(callsite.method);
        }
        for (String suffix : suffixes) {
            String callerProjection = callsite.receiver + suffix;
            String calleeProjection = calleeThis + suffix;
            if (addEdge("method_receiver_field", callerProjection, calleeProjection,
                    callsite.method, callsite.fact,
                    "instance method receiver field flows to callee this field")) {
                changed = true;
            }
            changed |= relevant(callsite.method).add(callerProjection);
            changed |= selectedMethods.add(callsite.method);
        }
        return changed;
    }

    private boolean expandConstructorReceiverFields(String constructor, String constructorThis,
                                                    Set<String> suffixes,
                                                    ConstructorCallsite callsite) {
        if (constructorThis == null || ignoreNode(callsite.receiver)) {
            return false;
        }
        boolean changed = false;
        if (relevant(constructor).contains(constructorThis)) {
            if (addEdge("constructor_receiver", callsite.receiver, constructorThis,
                    callsite.method, callsite.fact,
                    "constructor receiver aliases constructor this")) {
                changed = true;
            }
            changed |= relevant(callsite.method).add(callsite.receiver);
            changed |= selectedMethods.add(callsite.method);
        }
        for (String suffix : suffixes) {
            String constructorProjection = constructorThis + suffix;
            String callerProjection = callsite.receiver + suffix;
            if (addEdge("constructor_receiver_field", constructorProjection,
                    callerProjection, callsite.method, callsite.fact,
                    "constructor-written this field is visible on caller receiver")) {
                changed = true;
            }
            changed |= relevant(callsite.method).add(callerProjection);
            changed |= selectedMethods.add(callsite.method);
        }
        return changed;
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

    private boolean relevantContainsProjectionOrExact(Set<String> relevant, String node) {
        if (node == null || relevant.contains(node)) {
            return node != null && relevant.contains(node);
        }
        for (String value : relevant) {
            if (value.startsWith(node + "#field:")) {
                return true;
            }
        }
        return false;
    }

    private Set<String> projectionSuffixesForBase(String method, String base) {
        Set<String> suffixes = new LinkedHashSet<>();
        if (base == null || base.isEmpty()) {
            return suffixes;
        }
        Set<String> methodRelevant = relevantByMethod.get(method);
        if (methodRelevant != null) {
            collectProjectionSuffixes(methodRelevant, base, suffixes);
        }
        for (Set<String> relevant : relevantByMethod.values()) {
            collectProjectionSuffixes(relevant, base, suffixes);
        }
        return suffixes;
    }

    private void collectProjectionSuffixes(Set<String> relevant, String base,
                                           Set<String> suffixes) {
        String prefix = base + "#field:";
        for (String value : relevant) {
            if (value.startsWith(prefix)) {
                suffixes.add(value.substring(base.length()));
            }
        }
    }

    private boolean addProjectedRelevance(String method, String node) {
        if (ignoreNode(node)) {
            return false;
        }
        String owner = methodForCell(node, method);
        return relevant(owner).add(node);
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

    private String accessorFieldName(String methodName) {
        if (methodName == null || methodName.isEmpty()) {
            return "";
        }
        String stem = "";
        if (methodName.startsWith("get") && methodName.length() > 3) {
            stem = methodName.substring(3);
        } else if (methodName.startsWith("is") && methodName.length() > 2) {
            stem = methodName.substring(2);
        }
        if (stem.isEmpty()) {
            return "";
        }
        if (stem.length() == 1) {
            return stem.toLowerCase(Locale.ROOT);
        }
        return Character.toLowerCase(stem.charAt(0)) + stem.substring(1);
    }

    private static String fieldNameFromSignature(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = Pattern.compile("<[^:]+:\\s+.+\\s+([^\\s>]+)>")
                .matcher(fieldSignature);
        return matcher.find() ? matcher.group(1) : "";
    }

    private boolean addProjectedEdgesForObjectFlow(String kind, String fromText,
                                                   String toText, String method,
                                                   Fact fact,
                                                   Map<String, Object> baseEdge) {
        if (!supportsProjectedPropagation(kind)
                || ("local_def_use".equals(kind) && fact != null
                && fact.invoke != null)
                || !canCarryProjectedFields(fromText)
                || !canCarryProjectedFields(toText)) {
            return false;
        }
        String baseEdgeId = baseEdge == null ? ""
                : stringValue(baseEdge.get("id"));
        Set<String> suffixes = new LinkedHashSet<>();
        suffixes.addAll(projectionSuffixesForBase(method, fromText));
        suffixes.addAll(projectionSuffixesForBase(method, toText));
        if (suffixes.isEmpty()) {
            return false;
        }
        boolean changed = false;
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
            if (addEdgeInternal("projected_" + kind, fromProjection, toProjection,
                    method, fact,
                    "field path propagated along object edge " + baseEdgeId,
                    false, baseEdge)) {
                changed = true;
            }
            if (isRelevantProjection(toText, suffix)) {
                changed |= addProjectedRelevance(method, fromProjection);
            }
            if (isRelevantProjection(fromText, suffix)) {
                changed |= addProjectedRelevance(method, toProjection);
            }
        }
        return changed;
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
        String projection = base + suffix;
        for (Set<String> relevant : relevantByMethod.values()) {
            if (relevant.contains(projection)) {
                return true;
            }
        }
        return false;
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
                for (SootField field : sootClass.getFields()) {
                    if (fieldName.equals(field.getName())) {
                        return field;
                    }
                }
                // Java class-field lookup checks the superclass chain;
                // interfaces are retained as a deterministic fallback for
                // inherited constants and interface-declared state.
                if (sootClass.hasSuperclass()) {
                    work.addFirst(sootClass.getSuperclass());
                }
                for (SootClass iface : sootClass.getInterfaces()) {
                    work.addLast(iface);
                }
            } catch (RuntimeException exception) {
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

    private boolean addEdge(String kind, Object from, Object to, String method,
                            Fact fact, String evidence) {
        return addEdgeInternal(kind, from, to, method, fact, evidence, true);
    }

    private boolean addEdgeInternal(String kind, Object from, Object to, String method,
                                    Fact fact, String evidence,
                                    boolean deriveProjectedEdges) {
        return addEdgeInternal(kind, from, to, method, fact, evidence,
                deriveProjectedEdges, null);
    }

    private boolean addEdgeInternal(String kind, Object from, Object to, String method,
                                    Fact fact, String evidence,
                                    boolean deriveProjectedEdges,
                                    Map<String, Object> projectionBaseEdge) {
        if (edges.size() >= maxEdges || from == null || to == null) {
            return false;
        }
        String fromText = String.valueOf(from);
        String toText = String.valueOf(to);
        boolean sameCellPathGuard =
                ControlDependenceEdgeSupport.permitsSameCellEdge(kind,
                        fromText, toText, fact != null);
        if (ignoreNode(fromText) || ignoreNode(toText)
                || fromText.equals(toText) && !sameCellPathGuard) {
            return false;
        }
        String key = edgeKey(kind, fromText, toText, method, fact);
        boolean changed = false;
        Map<String, Object> edge = emittedEdgeRows.get(key);
        if (edge == null) {
            String edgeId = "DF." + edgeCounter++;
            boolean ownMappingOnly = isStaticPortMappingKind(kind);
            boolean hasProjectionBase = projectionBaseEdge != null;
            // A projected row is a derived view of its base edge.  Its
            // rendered kind must never manufacture stronger semantic
            // authority than that base.  In particular, a static
            // format/port mapping remains mapping-only after field
            // projection.  Require an explicit false/true tuple on the
            // base so older or incomplete rows fail closed.
            boolean baseMappingOnly = hasProjectionBase
                    && !Boolean.FALSE.equals(
                    projectionBaseEdge.get("mappingOnly"));
            boolean mappingOnly = ownMappingOnly || baseMappingOnly;
            boolean baseSemanticAssertionsAllowed = !hasProjectionBase
                    || Boolean.TRUE.equals(projectionBaseEdge.get(
                    "semanticAssertionsAllowed"));
            boolean baseAutomaticDerivationAllowed = !hasProjectionBase
                    || Boolean.TRUE.equals(projectionBaseEdge.get(
                    "eligibleForAutomaticDerivation"));
            boolean baseAutomaticSmtAllowed = !hasProjectionBase
                    || Boolean.TRUE.equals(projectionBaseEdge.get(
                    "eligibleForAutomaticSmt"));
            boolean semanticAssertionsAllowed = !mappingOnly
                    && baseSemanticAssertionsAllowed;
            boolean eligibleForAutomaticDerivation =
                    semanticAssertionsAllowed
                            && baseAutomaticDerivationAllowed;
            boolean eligibleForAutomaticSmt = semanticAssertionsAllowed
                    && baseAutomaticSmtAllowed;
            String mappingAuthority = "";
            if (mappingOnly) {
                mappingAuthority = baseMappingOnly
                        ? stringValue(projectionBaseEdge.get(
                        "mappingAuthority"))
                        : "STATIC_FORMAT_AND_PORT_MAPPING";
            }
            String edgeTransferKind = SymbolicPlanningStage.transferKind(
                    kind,
                    fact == null ? "" : fact.unitText,
                    fact == null ? null : fact.invoke,
                    fromText, toText);
            boolean exactDirectCopy = !mappingOnly
                    && exactLocalDirectCopy(kind, fromText, toText,
                    method, fact, edgeTransferKind);
            boolean projectedDirectCopy = !mappingOnly
                    && exactProjectedDirectCopy(kind, fromText, toText,
                    projectionBaseEdge, edgeTransferKind);
            String relation = exactDirectCopy || projectedDirectCopy
                    ? "value_flow" : relationForKind(kind);
            edge = object(
                    "id", edgeId,
                    "kind", kind,
                    "transferKind", edgeTransferKind,
                    "relation", mappingOnly ? "" : relation,
                    "candidateRelation", relation,
                    "mappingOnly", mappingOnly,
                    "mappingAuthority", mappingAuthority,
                    "semanticAssertionsAllowed",
                    semanticAssertionsAllowed,
                    "eligibleForAutomaticDerivation",
                    eligibleForAutomaticDerivation,
                    "eligibleForAutomaticSmt", eligibleForAutomaticSmt,
                    "direction", "backward_provenance",
                    "fromCell", fromText,
                    "toCell", toText,
                    "method", method,
                    "siteId", stableSiteId(method,
                            fact == null ? -1 : fact.unitIndex, kind),
                    "evidence", evidence);
            if (hasProjectionBase) {
                edge.put("projectionBaseEdgeId", stringValue(
                        projectionBaseEdge.get("id")));
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
                String baseAuthority = stringValue(
                        projectionBaseEdge.get("valueFlowAuthority"));
                edge.put("valueFlowAuthority",
                        "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1".equals(
                                baseAuthority)
                                ? "PROJECTED_FROM_SOOT_EXACT_PARAMETER_"
                                + "IDENTITY_BINDING_V1"
                                : "PROJECTED_FROM_SOOT_EXACT_LOCAL_"
                                + "DIRECT_COPY_V1");
                edge.put("baseValueFlowEdgeId", stringValue(
                        projectionBaseEdge.get("id")));
                edge.put("baseValueFlowAuthority", stringValue(
                        projectionBaseEdge.get("valueFlowAuthority")));
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
                edge.put("line", fact.line);
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
            changed = true;
        }
        if (deriveProjectedEdges && edge != null) {
            changed |= addProjectedEdgesForObjectFlow(kind, fromText, toText,
                    method, fact, edge);
        }
        return changed;
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
            Map<String, Object> baseEdge, String edgeTransferKind) {
        if (!"projected_local_def_use".equals(kind)
                || !"VALUE_PASS".equals(edgeTransferKind)
                || baseEdge == null
                || !"local_def_use".equals(stringValue(
                baseEdge.get("kind")))
                || !"value_flow".equals(stringValue(
                baseEdge.get("relation")))
                || !"VALUE_PASS".equals(stringValue(
                baseEdge.get("transferKind")))
                || Boolean.TRUE.equals(baseEdge.get("mappingOnly"))
                || !Boolean.TRUE.equals(baseEdge.get(
                "semanticAssertionsAllowed"))
                || !Boolean.TRUE.equals(baseEdge.get(
                "eligibleForAutomaticDerivation"))
                || !Boolean.TRUE.equals(baseEdge.get(
                "eligibleForAutomaticSmt"))
                || !"backward_provenance".equals(stringValue(
                baseEdge.get("direction")))) {
            return false;
        }
        String authority = stringValue(baseEdge.get("valueFlowAuthority"));
        String copyKind = stringValue(baseEdge.get("directCopyKind"));
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
                && stripFieldProjection(fromText).equals(stringValue(
                baseEdge.get("fromCell")))
                && stripFieldProjection(toText).equals(stringValue(
                baseEdge.get("toCell")))
                && !stringValue(baseEdge.get("id")).isEmpty();
    }

    private String edgeKey(String kind, Object from, Object to,
                           String method) {
        return edgeKey(kind, from, to, method, null);
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

    private boolean isStaticPortMappingKind(String kind) {
        for (StaticPortMapping mapping : staticPortMappings) {
            if (mapping.kind.equals(kind)) return true;
        }
        return false;
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
                        "allocationConstructorUnitIndex",
                        candidate.unitIndex,
                        "allocationConstructorSiteId", stableSiteId(
                                method, candidate.unitIndex,
                                "allocation_constructor"),
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
                || kind.contains("sasl") || kind.contains("transfer")) {
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
                    || relevantContainsProjectionOrExact(relevant, value)) {
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

    private static MethodSig parseMethodSig(String raw) {
        if (raw == null || !raw.startsWith("<")) {
            return null;
        }
        Matcher matcher = Pattern.compile("<([^:]+):\\s+(.+)\\s+([^\\s(]+)\\((.*)\\)>")
                .matcher(raw);
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

    private static String ownerOf(String methodSignature) {
        MethodSig sig = parseMethodSig(methodSignature);
        return sig == null ? "" : sig.owner;
    }

    private static String stableSiteId(String method, int unitIndex, String kind) {
        if (unitIndex >= 0) {
            return method + "#u" + unitIndex;
        }
        return method + "#synthetic:" + firstNonBlank(kind, "edge");
    }

    private static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static List<String> sortedLimited(Set<String> values, int limit) {
        List<String> sorted = new ArrayList<>(values);
        Collections.sort(sorted);
        if (sorted.size() <= limit) {
            return sorted;
        }
        return new ArrayList<>(sorted.subList(0, limit));
    }

    private static Map<String, Object> summarizeEdgeKinds(List<Map<String, Object>> edges) {
        Map<String, Object> counts = object();
        for (Map<String, Object> edge : edges) {
            String kind = String.valueOf(edge.get("kind"));
            Object previous = counts.get(kind);
            counts.put(kind, previous instanceof Number
                    ? ((Number) previous).intValue() + 1 : 1);
        }
        return counts;
    }

    private static String cellKind(String cell) {
        if (cell.contains("#exception:")) {
            return "exception";
        }
        if (cell.contains(".param")) {
            return "parameter";
        }
        if (cell.endsWith(".return")) {
            return "return";
        }
        if (cell.contains("#u")) {
            return "unit";
        }
        if (cell.startsWith("<") && cell.contains(":")) {
            return cell.contains(" ") ? "field_or_method" : "signature";
        }
        if (cell.contains("::")) {
            return "local";
        }
        return "seed";
    }

    @SafeVarargs
    private static <T> List<T> concat(Collection<T>... lists) {
        List<T> result = new ArrayList<>();
        for (Collection<T> list : lists) {
            result.addAll(list);
        }
        return result;
    }

    private static boolean containsAny(String value, Collection<String> needles) {
        if (value == null) {
            return false;
        }
        for (String needle : needles) {
            if (needle != null && !needle.isEmpty() && value.contains(needle)) {
                return true;
            }
        }
        return false;
    }

    private static boolean containsAll(String value, Collection<String> needles) {
        if (value == null) {
            return false;
        }
        for (String needle : needles) {
            if (needle != null && !needle.isEmpty() && !value.contains(needle)) {
                return false;
            }
        }
        return true;
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
