package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.tagkit.LineNumberTag;
import soot.tagkit.SourceLineNumberTag;
import soot.tagkit.Tag;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
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

/**
 * Seed-only static backward data-flow analysis.
 *
 * <p>The base analysis starts from the seed variable list in target.yaml.
 * Local Java/Jimple calls, discovered RPC dispatches, interface dispatches, and
 * explicitly enabled protocol bridges all emit edges into the same static
 * data-flow graph.</p>
 */
public final class CausynthPipeline {
    private static final Logger LOG = LoggerFactory.getLogger(CausynthPipeline.class);
    private static final String TRACE_RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";

    private final GraphCheckerOptions options;
    private final int sootClassCount;
    private final int sootConcreteMethodCount;

    public CausynthPipeline(GraphCheckerOptions options, int sootClassCount,
                            int sootConcreteMethodCount) {
        this.options = options;
        this.sootClassCount = sootClassCount;
        this.sootConcreteMethodCount = sootConcreteMethodCount;
    }

    public void run() throws IOException {
        TargetContext target = TargetContext.resolve(options);
        if (target.seedVariables.isEmpty()) {
            LOG.info("Seed backward analysis skipped: no seed_variables in {}", target.specPath);
            return;
        }

        LOG.info("Seed backward analysis starts from {}", target.seedVariables);
        AnalysisResult result = new SeedBackwardStaticAnalyzer(target).analyze();
        instrumentRuntimeTrace(result);
        new OutputWriter(target, result).writeAll();
        LOG.info("Seed backward analysis wrote {} edges to {}",
                result.edges.size(), target.outputDir);
    }

    private void instrumentRuntimeTrace(AnalysisResult result) {
        if (!Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.trace"),
                System.getenv("CAUSYNTH_INSTRUMENT_TRACE"),
                "false"))) {
            return;
        }
        SootMethodRef recordRef = traceRecorderMethodRef();
        SootMethodRef recordFieldRef = traceRecorderFieldMethodRef();
        TraceFieldSelection traceFields = traceFieldSelection(result);
        int count = 0;
        int fieldCount = 0;
        for (Map<String, Object> methodRow : result.traceMethods) {
            String signature = String.valueOf(methodRow.get("method"));
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete() || method.isConstructor()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                Unit insertionPoint = firstNonIdentity(body);
                Value receiver = NullConstant.v();
                if (!method.isStatic()) {
                    try {
                        Local thisLocal = body.getThisLocal();
                        if (thisLocal != null) {
                            receiver = thisLocal;
                        }
                    } catch (RuntimeException ignored) {
                    }
                }
                Stmt traceCall = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                        recordRef, StringConstant.v(signature), receiver));
                if (insertionPoint == null) {
                    body.getUnits().add(traceCall);
                } else {
                    body.getUnits().insertBefore(traceCall, insertionPoint);
                }
                fieldCount += instrumentFieldTrace(body, method, recordFieldRef,
                        traceFields);
                count++;
            } catch (RuntimeException exception) {
                LOG.debug("Skipping trace instrumentation for {}", signature, exception);
            }
        }
        result.slices.put("traceInstrumentedMethodCount", count);
        result.slices.put("traceInstrumentedFieldAccessCount", fieldCount);
        LOG.info("Instrumented {} selected methods and {} field accesses for runtime trace",
                count, fieldCount);
    }

    private int instrumentFieldTrace(Body body, SootMethod method,
                                     SootMethodRef recordFieldRef,
                                     TraceFieldSelection traceFields) {
        List<Unit> units = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            units.add(unit);
        }
        int count = 0;
        Value methodReceiver = NullConstant.v();
        if (!method.isStatic()) {
            try {
                Local thisLocal = body.getThisLocal();
                if (thisLocal != null) {
                    methodReceiver = thisLocal;
                }
            } catch (RuntimeException ignored) {
            }
        }
        int unitIndex = 0;
        for (Unit unit : units) {
            if (!(unit instanceof Stmt)) {
                unitIndex++;
                continue;
            }
            Stmt stmt = (Stmt) unit;
            if (stmt instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) stmt;
                Value left = assign.getLeftOp();
                Value right = assign.getRightOp();
                if (left instanceof InstanceFieldRef) {
                    count += insertFieldTrace(body, unit, recordFieldRef, "FIELD_WRITE",
                            method.getSignature(), unitIndex, (InstanceFieldRef) left,
                            methodReceiver, right, true, traceFields);
                }
                if (right instanceof InstanceFieldRef) {
                    count += insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                            method.getSignature(), unitIndex, (InstanceFieldRef) right,
                            methodReceiver, left, true, traceFields);
                }
            } else {
                for (ValueBox box : stmt.getUseBoxes()) {
                    Value value = box.getValue();
                    if (value instanceof InstanceFieldRef) {
                        count += insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                                method.getSignature(), unitIndex, (InstanceFieldRef) value,
                                methodReceiver, value, false, traceFields);
                    }
                }
            }
            unitIndex++;
        }
        return count;
    }

    private int insertFieldTrace(Body body, Unit unit, SootMethodRef recordFieldRef,
                                 String kind, String method, int unitIndex,
                                 InstanceFieldRef fieldRef, Value methodReceiverValue,
                                 Value value,
                                 boolean fieldValueIsReadValue,
                                 TraceFieldSelection traceFields) {
        String field = fieldRef.getFieldRef().getSignature();
        if (!shouldInstrumentField(field, traceFields)) {
            return 0;
        }
        List<Unit> prefixUnits = new ArrayList<>();
        Value methodReceiver = objectArg(body, methodReceiverValue, prefixUnits);
        Value receiver = objectArg(body, fieldRef.getBase(), prefixUnits);
        Value valueObject = objectArg(body, value, prefixUnits);
        Value primitiveValue = primitiveValueString(body, value, prefixUnits);
        Stmt traceCall = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                recordFieldRef,
                StringConstant.v(kind),
                StringConstant.v(method),
                IntConstant.v(unitIndex),
                StringConstant.v(field),
                methodReceiver,
                receiver,
                valueObject,
                primitiveValue));
        if (fieldValueIsReadValue || "FIELD_WRITE".equals(kind)) {
            Unit anchor = unit;
            for (Unit prefixUnit : prefixUnits) {
                body.getUnits().insertAfter(prefixUnit, anchor);
                anchor = prefixUnit;
            }
            body.getUnits().insertAfter(traceCall, anchor);
        } else {
            Unit anchor = null;
            for (Unit prefixUnit : prefixUnits) {
                if (anchor == null) {
                    body.getUnits().insertBefore(prefixUnit, unit);
                } else {
                    body.getUnits().insertAfter(prefixUnit, anchor);
                }
                anchor = prefixUnit;
            }
            if (anchor == null) {
                body.getUnits().insertBefore(traceCall, unit);
            } else {
                body.getUnits().insertAfter(traceCall, anchor);
            }
        }
        return 1;
    }

    private static boolean shouldInstrumentField(String field,
                                                 TraceFieldSelection traceFields) {
        if (field == null || traceFields == null || traceFields.isEmpty()) {
            return false;
        }
        if (traceFields.signatures.contains(field)) {
            return true;
        }
        String fieldName = fieldNameFromSignature(field);
        return !fieldName.isEmpty() && traceFields.names.contains(fieldName);
    }

    private static TraceFieldSelection traceFieldSelection(AnalysisResult result) {
        TraceFieldSelection selection = new TraceFieldSelection();
        for (Map<String, Object> edge : result.edges) {
            collectTraceFields(selection, String.valueOf(edge.get("fromCell")));
            collectTraceFields(selection, String.valueOf(edge.get("toCell")));
            collectTraceFields(selection, String.valueOf(edge.get("objectFromCell")));
            collectTraceFields(selection, String.valueOf(edge.get("objectToCell")));
            collectFieldPathNames(selection, String.valueOf(edge.get("fieldPath")));
        }
        return selection;
    }

    private static void collectTraceFields(TraceFieldSelection selection, String cell) {
        if (cell == null || cell.isEmpty() || "null".equals(cell)) {
            return;
        }
        Matcher field = Pattern.compile("<[^:]+:\\s+[^()<>]+\\s+[^\\s()>]+>")
                .matcher(cell);
        while (field.find()) {
            String signature = field.group();
            if (parseMethodSig(signature) != null) {
                continue;
            }
            selection.signatures.add(signature);
            String fieldName = fieldNameFromSignature(signature);
            if (!fieldName.isEmpty()) {
                selection.names.add(fieldName);
            }
        }
        collectFieldPathNames(selection, cell);
    }

    private static void collectFieldPathNames(TraceFieldSelection selection, String text) {
        if (text == null || text.isEmpty() || "null".equals(text)) {
            return;
        }
        Matcher matcher = Pattern.compile("#field:([^#@]+)").matcher(text);
        while (matcher.find()) {
            String name = matcher.group(1).trim();
            if (!name.isEmpty()) {
                selection.names.add(name);
            }
        }
    }

    private static String fieldNameFromSignature(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = Pattern.compile("<[^:]+:\\s+.+\\s+([^\\s>]+)>")
                .matcher(fieldSignature);
        return matcher.find() ? matcher.group(1) : "";
    }

    private static Value objectArg(Body body, Value value, List<Unit> prefixUnits) {
        if (value == null || value instanceof NullConstant) {
            return NullConstant.v();
        }
        if (value.getType() instanceof RefType || value.getType() instanceof ArrayType) {
            return immediateValue(body, value, prefixUnits);
        }
        return NullConstant.v();
    }

    private static Value primitiveValueString(Body body, Value value, List<Unit> prefixUnits) {
        if (value == null || value instanceof NullConstant) {
            return StringConstant.v("");
        }
        SootClass stringClass = Scene.v().getSootClass("java.lang.String");
        if (value.getType() instanceof IntType) {
            SootMethodRef ref = Scene.v().makeMethodRef(stringClass, "valueOf",
                    Collections.singletonList(IntType.v()), RefType.v("java.lang.String"), true);
            return primitiveStringLocal(body, value, ref, prefixUnits);
        }
        if (value.getType() instanceof BooleanType) {
            SootMethodRef ref = Scene.v().makeMethodRef(stringClass, "valueOf",
                    Collections.singletonList(BooleanType.v()), RefType.v("java.lang.String"), true);
            return primitiveStringLocal(body, value, ref, prefixUnits);
        }
        if (value.getType() instanceof LongType) {
            SootMethodRef ref = Scene.v().makeMethodRef(stringClass, "valueOf",
                    Collections.singletonList(LongType.v()), RefType.v("java.lang.String"), true);
            return primitiveStringLocal(body, value, ref, prefixUnits);
        }
        return StringConstant.v("");
    }

    private static Value primitiveStringLocal(Body body, Value value, SootMethodRef ref,
                                             List<Unit> prefixUnits) {
        Value source = immediateValue(body, value, prefixUnits);
        Local tmp = newTraceLocal(body, RefType.v("java.lang.String"), "$causynthPrim");
        prefixUnits.add(Jimple.v().newAssignStmt(tmp,
                Jimple.v().newStaticInvokeExpr(ref, source)));
        return tmp;
    }

    private static Value immediateValue(Body body, Value value, List<Unit> prefixUnits) {
        if (value instanceof Local || value instanceof Constant) {
            return value;
        }
        Local tmp = newTraceLocal(body, value.getType(), "$causynthValue");
        prefixUnits.add(Jimple.v().newAssignStmt(tmp, value));
        return tmp;
    }

    private static Local newTraceLocal(Body body, Type type, String prefix) {
        int index = body.getLocals().size();
        while (true) {
            String name = prefix + index;
            boolean exists = false;
            for (Local local : body.getLocals()) {
                if (name.equals(local.getName())) {
                    exists = true;
                    break;
                }
            }
            if (!exists) {
                Local local = Jimple.v().newLocal(name, type);
                body.getLocals().add(local);
                return local;
            }
            index++;
        }
    }

    private static Unit firstNonIdentity(Body body) {
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof IdentityStmt)) {
                return unit;
            }
        }
        return null;
    }

    private static SootMethodRef traceRecorderMethodRef() {
        SootClass recorder = Scene.v().getSootClassUnsafe(TRACE_RECORDER_CLASS);
        if (recorder == null) {
            recorder = new SootClass(TRACE_RECORDER_CLASS, Modifier.PUBLIC);
            recorder.setPhantomClass();
            Scene.v().addClass(recorder);
        }
        return Scene.v().makeMethodRef(recorder, "record",
                Arrays.asList(RefType.v("java.lang.String"), RefType.v("java.lang.Object")),
                VoidType.v(), true);
    }

    private static SootMethodRef traceRecorderFieldMethodRef() {
        SootClass recorder = Scene.v().getSootClassUnsafe(TRACE_RECORDER_CLASS);
        if (recorder == null) {
            recorder = new SootClass(TRACE_RECORDER_CLASS, Modifier.PUBLIC);
            recorder.setPhantomClass();
            Scene.v().addClass(recorder);
        }
        return Scene.v().makeMethodRef(recorder, "recordField",
                Arrays.asList(
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        IntType.v(),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v(), true);
    }

    private static final class TraceFieldSelection {
        private final Set<String> signatures = new LinkedHashSet<>();
        private final Set<String> names = new LinkedHashSet<>();

        private boolean isEmpty() {
            return signatures.isEmpty() && names.isEmpty();
        }
    }

    private static final class TargetContext {
        private final Path repoRoot;
        private final Path moduleDir;
        private final Path outputDir;
        private final Path specPath;
        private final List<String> seedVariables;
        private final String seedFunction;
        private final String analysisScope;

        private TargetContext(Path repoRoot, Path moduleDir, Path outputDir,
                              Path specPath, List<String> seedVariables,
                              String seedFunction, String analysisScope) {
            this.repoRoot = repoRoot;
            this.moduleDir = moduleDir;
            this.outputDir = outputDir;
            this.specPath = specPath;
            this.seedVariables = seedVariables;
            this.seedFunction = seedFunction;
            this.analysisScope = analysisScope;
        }

        static TargetContext resolve(GraphCheckerOptions options) throws IOException {
            Map<String, String> config = readConfig(options.getConfigFilePath());
            Path specPath = Paths.get(firstNonBlank(
                    System.getProperty("causynth.target.spec"),
                    config.get("causynth_target_spec"),
                    "target.yaml")).toAbsolutePath().normalize();
            TargetSpec spec = TargetSpec.load(specPath);
            Path repo = Paths.get(firstNonBlank(
                    System.getProperty("causynth.repo"),
                    config.get("causynth_repo"),
                    config.get("system_dir_path"),
                    ".")).toAbsolutePath().normalize();
            Path module = Paths.get(firstNonBlank(
                    System.getProperty("causynth.module.dir"),
                    config.get("causynth_module_dir"),
                    repo.toString())).toAbsolutePath().normalize();
            Path output = Paths.get(firstNonBlank(
                    System.getProperty("causynth.output.dir"),
                    config.get("causynth_output_dir"),
                    "causynth-output/seed-backward")).toAbsolutePath().normalize();
            String scope = firstNonBlank(
                    System.getProperty("causynth.analysis.scope"),
                    config.get("causynth_analysis_scope"),
                    config.get("causynth_scope"),
                    "");
            return new TargetContext(repo, module, output, specPath,
                    spec.seedVariables, spec.seedFunction, scope);
        }

        String seedPredicate() {
            if (seedVariables.size() >= 2) {
                return seedVariables.get(0) + ".get(" + seedVariables.get(1) + ") == null";
            }
            return seedVariables.get(0);
        }

        String seedMapName() {
            return seedVariables.isEmpty() ? "" : seedVariables.get(0);
        }

        String seedKeyExpression() {
            return seedVariables.size() < 2 ? "" : seedVariables.get(1);
        }

        String seedKeyMethodName() {
            Matcher dottedCall = Pattern.compile("\\.\\s*([A-Za-z_][A-Za-z0-9_]*)\\s*\\(")
                    .matcher(seedKeyExpression());
            if (dottedCall.find()) {
                return dottedCall.group(1);
            }
            Matcher bareCall = Pattern.compile("^\\s*([A-Za-z_][A-Za-z0-9_]*)\\s*\\(")
                    .matcher(seedKeyExpression());
            if (bareCall.find()) {
                return bareCall.group(1);
            }
            return "";
        }
    }

    private static final class TargetSpec {
        private final List<String> seedVariables;
        private final String seedFunction;

        private TargetSpec(List<String> seedVariables, String seedFunction) {
            this.seedVariables = seedVariables;
            this.seedFunction = seedFunction;
        }

        static TargetSpec load(Path path) throws IOException {
            if (!Files.isRegularFile(path)) {
                return new TargetSpec(Collections.emptyList(), null);
            }
            List<String> variables = new ArrayList<>();
            String seedFunction = null;
            boolean inSeedVariables = false;
            for (String line : Files.readAllLines(path, StandardCharsets.UTF_8)) {
                String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                    continue;
                }
                if (!line.startsWith(" ") && trimmed.contains(":")
                        && !trimmed.endsWith(":")) {
                    String key = trimmed.substring(0, trimmed.indexOf(':')).trim();
                    String value = unquote(trimmed.substring(trimmed.indexOf(':') + 1)
                            .trim());
                    if ("seed_function".equals(key) || "seed_method".equals(key)) {
                        seedFunction = value;
                    }
                    inSeedVariables = false;
                    continue;
                }
                if (!line.startsWith(" ") && trimmed.endsWith(":")) {
                    inSeedVariables = "seed_variables".equals(trimmed.substring(0,
                            trimmed.length() - 1));
                    continue;
                }
                if (inSeedVariables && trimmed.startsWith("- ")) {
                    String variable = trimmed.substring(2).trim();
                    if (!variable.isEmpty()) {
                        variables.add(variable);
                    }
                }
            }
            return new TargetSpec(variables, seedFunction);
        }

        private static String unquote(String value) {
            if ((value.startsWith("\"") && value.endsWith("\""))
                    || (value.startsWith("'") && value.endsWith("'"))) {
                return value.substring(1, value.length() - 1);
            }
            return value;
        }
    }

    private static final class AnalysisResult {
        private final List<Map<String, Object>> seeds = new ArrayList<>();
        private final List<Map<String, Object>> cells = new ArrayList<>();
        private final List<Map<String, Object>> edges = new ArrayList<>();
        private final List<Map<String, Object>> traceMethods = new ArrayList<>();
        private final Map<String, Object> slices = object();
        private final Map<String, Object> targetResolved = object();
    }

    private static final class SeedBackwardStaticAnalyzer {
        private static final int MAX_ROUNDS = 96;
        private static final int MAX_METHODS = 1000;
        private static final int MAX_EDGES = 50000;
        private static final int MAX_RPC_TARGETS_PER_CALL = 6;
        private static final int MAX_DISPATCH_TARGETS_PER_CALL = 8;
        private static final int MAX_CONSTRUCTOR_CALLERS_PER_PARAM = 80;
        private static final int MAX_METHOD_CALLERS_PER_METHOD = 200;
        private static final int MAX_FIELD_WRITERS_PER_FIELD = 80;
        private static final int MAX_FIELD_PATH_DEPTH = 4;
        private static final String HDFS_SASL_CLIENT =
                "org.apache.hadoop.hdfs.protocol.datatransfer.sasl.SaslDataTransferClient";
        private static final String HDFS_SASL_SERVER =
                "org.apache.hadoop.hdfs.protocol.datatransfer.sasl.SaslDataTransferServer";

        private final TargetContext target;
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
        private final List<HardCodedDataflow> hardCodedDataflows = new ArrayList<>();
        private final Map<String, Set<String>> relevantByMethod = new LinkedHashMap<>();
        private final Set<String> selectedMethods = new LinkedHashSet<>();
        private final Set<String> emittedEdges = new LinkedHashSet<>();
        private final Set<String> emittedRpcMappings = new LinkedHashSet<>();
        private final Set<String> emittedHardCodedDataflows = new LinkedHashSet<>();
        private final Set<String> expandedFieldWriterFields = new LinkedHashSet<>();
        private final Set<String> expandedConstructorCallees = new LinkedHashSet<>();
        private final Set<String> expandedMethodCallerKeys = new LinkedHashSet<>();
        private final Map<String, Boolean> receiverProjectionWriteSummary =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> projectionAliasCache =
                new LinkedHashMap<>();
        private final List<Map<String, Object>> edges = new ArrayList<>();
        private boolean globalStaticIndexBuilt;
        private int edgeCounter;
        private int projectedPassEdgeChecks;
        private int projectedPassUnsupported;
        private int projectedPassNoSuffix;
        private int projectedPassCandidates;
        private int projectedPassEmitted;

        private SeedBackwardStaticAnalyzer(TargetContext target) {
            this.target = target;
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
                buildHardCodedSaslHandshakeDataflows();
            } else {
                buildRpcMappings();
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

        private void buildHardCodedSaslHandshakeDataflows() {
            SootMethod clientHandshake = findMethod(HDFS_SASL_CLIENT,
                    "doSaslHandshake", 6);
            MethodSig clientSig = clientHandshake == null
                    ? null
                    : parseMethodSig(clientHandshake.getSignature());
            if (clientSig == null || clientSig.params.size() <= 3) {
                return;
            }
            String clientUserName = formalParam(clientSig, 3);

            for (HardCodedEndpoint endpoint : hdfsSaslServerUserNameEndpoints()) {
                addHardCodedDataflow("hdfs_sasl_username",
                        clientHandshake.getSignature(), clientUserName,
                        endpoint.method, endpoint.cell,
                        "HDFS SASL handshake transports client userName to server NameCallback defaultName");
            }
            LOG.info("Discovered {} hard-coded data-flow mappings",
                    hardCodedDataflows.size());
        }

        private List<HardCodedEndpoint> hdfsSaslServerUserNameEndpoints() {
            List<HardCodedEndpoint> endpoints = new ArrayList<>();
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
                        endpoints.add(new HardCodedEndpoint(handle.getSignature(), cell));
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

        private void addHardCodedDataflow(String kind, String sourceMethod,
                                          String sourceCell, String targetMethod,
                                          String targetCell, String evidence) {
            String key = kind + "\n" + sourceCell + "\n" + targetCell;
            if (!emittedHardCodedDataflows.add(key)) {
                return;
            }
            hardCodedDataflows.add(new HardCodedDataflow(kind, sourceMethod,
                    sourceCell, targetMethod, targetCell, evidence));
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

        AnalysisResult analyze() throws IOException {
            AnalysisResult result = new AnalysisResult();
            result.targetResolved.put("seedVariables", target.seedVariables);
            result.targetResolved.put("seedFunction", target.seedFunction);
            result.targetResolved.put("seedPredicate", target.seedPredicate());
            result.targetResolved.put("seedMap", target.seedMapName());
            result.targetResolved.put("seedKeyExpression", target.seedKeyExpression());
            result.targetResolved.put("analysisScope", target.analysisScope);
            result.targetResolved.put("repoRoot", target.repoRoot.toString());
            result.targetResolved.put("moduleDir", target.moduleDir.toString());

            result.seeds.add(object(
                    "id", "seed.local_condition",
                    "kind", "local_condition",
                    "predicate", target.seedPredicate(),
                    "variables", target.seedVariables));

            if (isHdfsKeyPropagationFastPathTarget()) {
                Set<String> candidateClasses = hdfsPropagationClasses();
                loadScopedHdfsPropagationMethods(candidateClasses);
                initializeSeedAnchors();
                initializeHdfsDirectLookupSeedAnchors();
                runWorklist();

                result.edges.addAll(edges);
                result.cells.addAll(collectCells());
                result.traceMethods.addAll(collectLoadedTraceMethods());
                result.slices.put("strategy",
                        "HDFS-scoped seed backward static analysis over the NameNode/Balancer/DataNode block-key propagation chain");
                result.slices.put("candidateClassCount", candidateClasses.size());
                result.slices.put("rpcMappingCount", emittedRpcMappings.size());
                result.slices.put("hardCodedDataflowCount", hardCodedDataflows.size());
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
                result.slices.put("loadedMethodCount", factsByMethod.size());
                result.slices.put("selectedMethodCount", selectedMethods.size());
                result.slices.put("edgeCount", edges.size());
                result.slices.put("edgeKinds", summarizeEdgeKinds(edges));
                result.slices.put("projectedPassEdgeChecks", projectedPassEdgeChecks);
                result.slices.put("projectedPassUnsupported", projectedPassUnsupported);
                result.slices.put("projectedPassNoSuffix", projectedPassNoSuffix);
                result.slices.put("projectedPassCandidates", projectedPassCandidates);
                result.slices.put("projectedPassEmitted", projectedPassEmitted);
                return result;
            }

            Set<String> candidateClasses = findCandidateClasses();
            loadClasses(candidateClasses);
            loadHardCodedDataflowClasses();
            initializeSeedAnchors();
            runWorklist();

            result.edges.addAll(edges);
            result.cells.addAll(collectCells());
            result.traceMethods.addAll(collectTraceMethods());
            result.slices.put("strategy",
                    "seed-only backward static analysis over Jimple def-use, calls, field writers, RPC mappings, and hard-coded SASL handshake dataflow");
            result.slices.put("candidateClassCount", candidateClasses.size());
            result.slices.put("rpcMappingCount", emittedRpcMappings.size());
            result.slices.put("hardCodedDataflowCount", hardCodedDataflows.size());
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
            result.slices.put("loadedMethodCount", factsByMethod.size());
            result.slices.put("selectedMethodCount", selectedMethods.size());
            result.slices.put("edgeCount", edges.size());
            result.slices.put("edgeKinds", summarizeEdgeKinds(edges));
            result.slices.put("projectedPassEdgeChecks", projectedPassEdgeChecks);
            result.slices.put("projectedPassUnsupported", projectedPassUnsupported);
            result.slices.put("projectedPassNoSuffix", projectedPassNoSuffix);
            result.slices.put("projectedPassCandidates", projectedPassCandidates);
            result.slices.put("projectedPassEmitted", projectedPassEmitted);
            return result;
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
                    HDFS_SASL_SERVER + "$SaslServerCallbackHandler"));
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
                        || owner.contains("SaslDataTransfer");
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
                        || (sourceClasses.isEmpty() && classFieldsTouchSeed(sootClass))) {
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
                if (containsAny(field.getName(), target.seedVariables)
                        || containsAny(field.getSignature(), target.seedVariables)) {
                    return true;
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

        private void loadHardCodedDataflowClasses() {
            if (hardCodedDataflows.isEmpty()) {
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

        private Collection<SootMethod> methodsForStaticIndex() {
            if (!isHdfsKeyPropagationFastPathTarget()) {
                return methodsBySignature.values();
            }
            List<SootMethod> scoped = new ArrayList<>();
            for (String signature : factsByMethod.keySet()) {
                SootMethod method = methodsBySignature.get(signature);
                if (method != null) {
                    scoped.add(method);
                }
            }
            return scoped;
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
            for (int round = 0; round < MAX_ROUNDS && edges.size() < MAX_EDGES; round++) {
                boolean changed = false;
                List<String> methodsThisRound = new ArrayList<>(selectedMethods);
                for (String method : methodsThisRound) {
                    changed |= processMethod(method);
                    changed |= expandCallers(method);
                    changed |= expandRpcCallers(method);
                    changed |= expandDispatchCallers(method);
                    changed |= expandHardCodedDataflows(method);
                    changed |= expandFieldWriters(method);
                    changed |= expandConstructorCallers(method);
                    changed |= expandMethodCallers(method);
                    if (selectedMethods.size() >= MAX_METHODS || edges.size() >= MAX_EDGES) {
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
                        if ((receiverExactHit || classFieldHit)
                                && canOpenFieldFromPlainValue(source)) {
                            changed |= relevant.add(source);
                        }
                    }
                }
            }
            for (String mutatedField : fieldsMutatedByInvoke(facts, fact.unitIndex)) {
                changed |= processFieldWrite(method, fact, relevant, mutatedField,
                        fieldMutationSources(method, fact, mutatedField),
                        "field_mutation",
                        "mutator call updates object stored in relevant field");
            }
            return changed;
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
                            || selectedMethods.size() >= MAX_METHODS
                            || edges.size() >= MAX_EDGES) {
                        break;
                    }
                    SootMethod writerMethod = methodsBySignature.get(writer.method);
                    if (writerMethod != null && loadMethod(writerMethod)) {
                        changed = true;
                    }
                    Set<String> writerRelevant = relevant(writer.method);
                    writerRelevant.add(writer.field);
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
                    if (selectedMethods.size() >= MAX_METHODS
                            || edges.size() >= MAX_EDGES
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
                        || selectedMethods.size() >= MAX_METHODS
                        || edges.size() >= MAX_EDGES) {
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
                List<Fact> facts = factsByMethod.get(method.getSignature());
                if (facts == null) {
                    facts = factsFromMethod(method);
                }
                if (facts.isEmpty()) {
                    continue;
                }
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
            }
            return fields;
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
            changed |= processAccessorInvoke(callerMethod, fact, callee, defs,
                    callerRelevant);
            List<String> actuals = canonicalPositionList(callerMethod,
                    actualInvokeArgs(fact.unitText));
            changed |= processConstructorObjectInvoke(callerMethod, fact, callee,
                    actuals, callerRelevant);
            boolean expandableCallee = isExpandableMethod(callee.raw);
            SootMethod calleeMethod = expandableCallee ? methodsBySignature.get(callee.raw) : null;
            if (expandableCallee && selectedMethods.size() < MAX_METHODS) {
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
                if (formalHit || actualHit) {
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
                if (defHit) {
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
            changed |= processRpcInvoke(callerMethod, fact, callee, defs, actuals,
                    callerRelevant);
            changed |= processDispatchInvoke(callerMethod, fact, callee, defs, actuals,
                    callerRelevant);
            return changed;
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
            if (!callerRelevant.contains(callerReceiver)
                    || containsProjection(callerRelevant, callerReceiver)) {
                return false;
            }
            boolean changed = false;
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
            if (cellValueType(receiverField).isEmpty()) {
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
                if (addEdge("accessor_field_return", receiverField, def,
                        callerMethod, fact,
                        "accessor return reads receiver field")) {
                    changed = true;
                }
            }
            if (defExactHit && canOpenFieldFromPlainValues(defs)) {
                changed |= callerRelevant.add(receiverField);
            }
            if (defProjectionHit) {
                changed |= callerRelevant.add(receiverField);
            }
            return changed;
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
                if (selectedMethods.size() < MAX_METHODS) {
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
                if (selectedMethods.size() < MAX_METHODS) {
                    loadMethod(sootMethod);
                }
                MethodSig targetSig = parseMethodSig(targetMethod);
                if (targetSig == null) {
                    continue;
                }
                Set<String> targetRelevant = relevant(targetMethod);
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
                    boolean defHit = defExactHit || defProjectionHit;
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
                    }
                }
            }
            return changed;
        }

        private List<String> resolveDispatchTargets(MethodSig callee) {
            if (callee == null || methodsBySignature.containsKey(callee.raw)
                    || skipDispatchOwner(callee.owner)
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
                if (selectedMethods.size() >= MAX_METHODS) {
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
                    if (selectedMethods.size() >= MAX_METHODS) {
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
                    if (selectedMethods.size() >= MAX_METHODS) {
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

        private boolean expandHardCodedDataflows(String method) {
            if (hardCodedDataflows.isEmpty()) {
                return false;
            }
            boolean changed = false;
            Set<String> methodRelevant = relevant(method);
            for (HardCodedDataflow dataflow : hardCodedDataflows) {
                if (dataflow.targetMethod.equals(method)
                        && methodRelevant.contains(dataflow.targetCell)) {
                    if (loadMethod(methodsBySignature.get(dataflow.sourceMethod))) {
                        changed = true;
                    }
                    Set<String> sourceRelevant = relevant(dataflow.sourceMethod);
                    if (addEdge(dataflow.kind, dataflow.sourceCell, dataflow.targetCell,
                            dataflow.targetMethod, null, dataflow.evidence)) {
                        changed = true;
                    }
                    changed |= sourceRelevant.add(dataflow.sourceCell);
                    changed |= selectedMethods.add(dataflow.sourceMethod);
                }
                if (dataflow.sourceMethod.equals(method)
                        && methodRelevant.contains(dataflow.sourceCell)) {
                    if (loadMethod(methodsBySignature.get(dataflow.targetMethod))) {
                        changed = true;
                    }
                    Set<String> targetRelevant = relevant(dataflow.targetMethod);
                    if (addEdge(dataflow.kind, dataflow.sourceCell, dataflow.targetCell,
                            dataflow.targetMethod, null, dataflow.evidence)) {
                        changed = true;
                    }
                    changed |= targetRelevant.add(dataflow.targetCell);
                    changed |= selectedMethods.add(dataflow.targetMethod);
                }
            }
            return changed;
        }

        private boolean propagateProjectedEdgesFromExistingEdges() {
            if (edges.isEmpty() || edges.size() >= MAX_EDGES) {
                return false;
            }
            boolean changed = false;
            List<Map<String, Object>> snapshot = new ArrayList<>(edges);
            for (Map<String, Object> edge : snapshot) {
                if (edges.size() >= MAX_EDGES) {
                    break;
                }
                String kind = String.valueOf(edge.get("kind"));
                String from = String.valueOf(edge.get("fromCell"));
                String to = String.valueOf(edge.get("toCell"));
                String method = String.valueOf(edge.get("method"));
                String edgeId = String.valueOf(edge.get("id"));
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
                        null, edgeId)) {
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
                    && !isAccessor(sig);
        }

        private boolean isAccessor(MethodSig sig) {
            if (sig == null) {
                return false;
            }
            if ("get".equals(sig.name)) {
                return true;
            }
            if (!sig.params.isEmpty()) {
                return false;
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
            List<String> uses = new ArrayList<>();
            for (String use : nonInvokeUses(fact)) {
                if (instanceFieldBases.contains(use)
                        || (!valueLikeLibraryInvoke && use.equals(invokeBase))
                        || applicationInvokeArgs.contains(use)
                        || isFieldAccessValue(use)) {
                    continue;
                }
                uses.add(use);
            }
            return uses;
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
                                                       Fact fact, String baseEdgeId) {
            if (!supportsProjectedPropagation(kind)
                    || ("local_def_use".equals(kind) && fact != null
                    && fact.invoke != null)
                    || !canCarryProjectedFields(fromText)
                    || !canCarryProjectedFields(toText)) {
                return false;
            }
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
                        false)) {
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
            String owner = erasedTypeName(ownerType);
            if (owner.isEmpty() || fieldName == null || fieldName.isEmpty()
                    || owner.endsWith("[]")) {
                return "";
            }
            SootClass sootClass = classesByName.get(owner);
            while (sootClass != null) {
                try {
                    for (SootField field : sootClass.getFields()) {
                        if (fieldName.equals(field.getName())) {
                            return field.getType().toString();
                        }
                    }
                    sootClass = sootClass.hasSuperclass() ? sootClass.getSuperclass() : null;
                } catch (RuntimeException exception) {
                    return "";
                }
            }
            return "";
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
            if (edges.size() >= MAX_EDGES || from == null || to == null) {
                return false;
            }
            String fromText = String.valueOf(from);
            String toText = String.valueOf(to);
            if (ignoreNode(fromText) || ignoreNode(toText) || fromText.equals(toText)) {
                return false;
            }
            String key = kind + "\n" + fromText + "\n" + toText + "\n" + method;
            boolean changed = false;
            String edgeId = kind + ":" + fromText + "->" + toText;
            if (emittedEdges.add(key)) {
                edgeId = "DF." + edgeCounter++;
                Map<String, Object> edge = object(
                        "id", edgeId,
                        "kind", kind,
                        "relation", relationForKind(kind),
                        "direction", "backward_provenance",
                        "fromCell", fromText,
                        "toCell", toText,
                        "method", method,
                        "evidence", evidence);
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
                }
                edges.add(edge);
                changed = true;
            }
            if (deriveProjectedEdges) {
                changed |= addProjectedEdgesForObjectFlow(kind, fromText, toText,
                        method, fact, edgeId);
            }
            return changed;
        }

        private String relationForKind(String kind) {
            if (kind == null) {
                return "taint_depends_on";
            }
            if (kind.contains("guard") || kind.contains("throw")) {
                return "control_depends_on";
            }
            if (kind.contains("field") || kind.contains("argument")
                    || kind.contains("return") || kind.contains("rpc")
                    || kind.contains("dispatch") || kind.contains("hdfs_sasl")) {
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
    }

    private static final class SeedLookupAnchor {
        private final List<Fact> seedFieldFacts;
        private final Set<String> seedValues;

        private SeedLookupAnchor(List<Fact> seedFieldFacts, Set<String> seedValues) {
            this.seedFieldFacts = seedFieldFacts;
            this.seedValues = seedValues;
        }
    }

    private static final class RpcTarget {
        private final String sourceSignature;
        private final String targetSignature;
        private final String kind;

        private RpcTarget(String sourceSignature, String targetSignature, String kind) {
            this.sourceSignature = sourceSignature;
            this.targetSignature = targetSignature;
            this.kind = kind;
        }
    }

    private static final class HardCodedDataflow {
        private final String kind;
        private final String sourceMethod;
        private final String sourceCell;
        private final String targetMethod;
        private final String targetCell;
        private final String evidence;

        private HardCodedDataflow(String kind, String sourceMethod, String sourceCell,
                                  String targetMethod, String targetCell,
                                  String evidence) {
            this.kind = kind;
            this.sourceMethod = sourceMethod;
            this.sourceCell = sourceCell;
            this.targetMethod = targetMethod;
            this.targetCell = targetCell;
            this.evidence = evidence;
        }
    }

    private static final class HardCodedEndpoint {
        private final String method;
        private final String cell;

        private HardCodedEndpoint(String method, String cell) {
            this.method = method;
            this.cell = cell;
        }
    }

    private static final class FieldWrite {
        private final String method;
        private final String field;
        private final Fact fact;
        private final String kind;
        private final List<String> sources;
        private final String evidence;

        private FieldWrite(String method, String field, Fact fact, String kind,
                           List<String> sources, String evidence) {
            this.method = method;
            this.field = field;
            this.fact = fact;
            this.kind = kind;
            this.sources = sources;
            this.evidence = evidence;
        }
    }

    private static final class ConstructorCallsite {
        private final String method;
        private final String constructor;
        private final Fact fact;
        private final String receiver;
        private final List<String> actuals;

        private ConstructorCallsite(String method, String constructor, Fact fact,
                                    String receiver, List<String> actuals) {
            this.method = method;
            this.constructor = constructor;
            this.fact = fact;
            this.receiver = receiver;
            this.actuals = actuals;
        }
    }

    private static final class MethodCallsite {
        private final String method;
        private final String callee;
        private final Fact fact;
        private final String receiver;
        private final List<String> actuals;
        private final List<String> defs;

        private MethodCallsite(String method, String callee, Fact fact,
                               String receiver, List<String> actuals, List<String> defs) {
            this.method = method;
            this.callee = callee;
            this.fact = fact;
            this.receiver = receiver;
            this.actuals = actuals;
            this.defs = defs;
        }
    }

    private static final class ConstructorParam {
        private final String constructor;
        private final int index;
        private final String formal;

        private ConstructorParam(String constructor, int index, String formal) {
            this.constructor = constructor;
            this.index = index;
            this.formal = formal;
        }
    }

    private static final class Fact {
        private final String method;
        private final int unitIndex;
        private final int line;
        private final String unitText;
        private final List<String> defs;
        private final List<String> uses;
        private final List<String> fields;
        private final List<String> fieldDefs;
        private final List<String> fieldUses;
        private final List<InstanceFieldAccess> instanceFieldDefs;
        private final List<InstanceFieldAccess> instanceFieldUses;
        private final String invoke;
        private final boolean isReturn;
        private final boolean isThrow;
        private final boolean isBranch;

        private Fact(String method, int unitIndex, Unit unit) {
            this.method = method;
            this.unitIndex = unitIndex;
            this.line = lineOf(unit);
            this.unitText = unit.toString();
            this.defs = valueStrings(unit.getDefBoxes());
            this.uses = valueStrings(unit.getUseBoxes());
            this.fields = fieldRefs(unit);
            this.fieldDefs = fieldRefs(unit.getDefBoxes());
            this.fieldUses = fieldRefs(unit.getUseBoxes());
            this.instanceFieldDefs = instanceFieldRefs(unit.getDefBoxes());
            this.instanceFieldUses = instanceFieldRefs(unit.getUseBoxes());
            this.invoke = invokeSignature(unit);
            String lower = unitText.trim().toLowerCase(Locale.ROOT);
            this.isReturn = lower.startsWith("return");
            this.isThrow = lower.startsWith("throw ");
            this.isBranch = lower.startsWith("if ")
                    || lower.startsWith("tableswitch")
                    || lower.startsWith("lookupswitch");
        }

        private static String invokeSignature(Unit unit) {
            if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()) {
                return ((Stmt) unit).getInvokeExpr().getMethodRef().getSignature();
            }
            return null;
        }

        private static List<String> fieldRefs(Unit unit) {
            Set<String> fields = new LinkedHashSet<>();
            for (ValueBox box : unit.getUseAndDefBoxes()) {
                Value value = box.getValue();
                if (value instanceof FieldRef) {
                    fields.add(((FieldRef) value).getFieldRef().getSignature());
                }
            }
            return new ArrayList<>(fields);
        }

        private static List<String> fieldRefs(List<ValueBox> boxes) {
            Set<String> fields = new LinkedHashSet<>();
            for (ValueBox box : boxes) {
                Value value = box.getValue();
                if (value instanceof FieldRef) {
                    fields.add(((FieldRef) value).getFieldRef().getSignature());
                }
            }
            return new ArrayList<>(fields);
        }

        private static List<InstanceFieldAccess> instanceFieldRefs(List<ValueBox> boxes) {
            List<InstanceFieldAccess> accesses = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            for (ValueBox box : boxes) {
                Value value = box.getValue();
                if (value instanceof InstanceFieldRef) {
                    InstanceFieldRef ref = (InstanceFieldRef) value;
                    String base = ref.getBase().toString();
                    String field = ref.getFieldRef().getSignature();
                    String key = base + "\n" + field;
                    if (seen.add(key)) {
                        accesses.add(new InstanceFieldAccess(base, field));
                    }
                }
            }
            return accesses;
        }

        private static List<String> valueStrings(List<ValueBox> boxes) {
            List<String> values = new ArrayList<>();
            for (ValueBox box : boxes) {
                values.add(box.getValue().toString());
            }
            return values;
        }

        private static int lineOf(Unit unit) {
            for (Tag tag : unit.getTags()) {
                if (tag instanceof SourceLineNumberTag) {
                    return ((SourceLineNumberTag) tag).getStartLineNumber();
                }
                if (tag instanceof LineNumberTag) {
                    return ((LineNumberTag) tag).getLineNumber();
                }
            }
            return unit.getJavaSourceStartLineNumber();
        }
    }

    private static final class InstanceFieldAccess {
        private final String base;
        private final String field;

        private InstanceFieldAccess(String base, String field) {
            this.base = base;
            this.field = field;
        }
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

    private static String fieldOwner(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = Pattern.compile("<([^:]+):").matcher(fieldSignature);
        return matcher.find() ? matcher.group(1) : "";
    }

    private static List<String> actualInvokeArgs(String unit) {
        if (unit == null) {
            return Collections.emptyList();
        }
        int start = unit.lastIndexOf(">(");
        int end = unit.lastIndexOf(')');
        if (start < 0 || end <= start + 2) {
            return Collections.emptyList();
        }
        return splitTopLevelArgs(unit.substring(start + 2, end));
    }

    private static List<String> splitTopLevelArgs(String args) {
        if (args == null || args.trim().isEmpty()) {
            return Collections.emptyList();
        }
        List<String> values = new ArrayList<>();
        StringBuilder current = new StringBuilder();
        int depth = 0;
        for (int i = 0; i < args.length(); i++) {
            char ch = args.charAt(i);
            if (ch == '(' || ch == '<' || ch == '[') {
                depth++;
            } else if (ch == ')' || ch == '>' || ch == ']') {
                depth = Math.max(0, depth - 1);
            }
            if (ch == ',' && depth == 0) {
                String value = current.toString().trim();
                if (!value.isEmpty()) {
                    values.add(value);
                }
                current.setLength(0);
            } else {
                current.append(ch);
            }
        }
        String value = current.toString().trim();
        if (!value.isEmpty()) {
            values.add(value);
        }
        return values;
    }

    private static final class OutputWriter {
        private final TargetContext target;
        private final AnalysisResult result;
        private int fileCount;

        private OutputWriter(TargetContext target, AnalysisResult result) {
            this.target = target;
            this.result = result;
        }

        private void writeAll() throws IOException {
            Files.createDirectories(target.outputDir);
            Files.deleteIfExists(target.outputDir.resolve("static_rpc_mappings.jsonl"));
            Files.deleteIfExists(target.outputDir.resolve("static_hardcoded_dataflows.jsonl"));
            writeJson("target_resolved.json", result.targetResolved);
            writeJson("seeds.json", object("seeds", result.seeds));
            writeJsonl("static_cells.jsonl", result.cells);
            writeJsonl("static_dataflow_edges.jsonl", result.edges);
            writeJsonl("static_trace_methods.jsonl", result.traceMethods);
            writeJson("static_slices.json", result.slices);
        }

        private void writeJson(String fileName, Object value) throws IOException {
            Files.write(target.outputDir.resolve(fileName),
                    Json.write(value).getBytes(StandardCharsets.UTF_8));
            fileCount++;
        }

        private void writeJsonl(String fileName, List<Map<String, Object>> values)
                throws IOException {
            StringBuilder builder = new StringBuilder();
            for (Object value : values) {
                builder.append(Json.write(value)).append('\n');
            }
            Files.write(target.outputDir.resolve(fileName),
                    builder.toString().getBytes(StandardCharsets.UTF_8));
            fileCount++;
        }
    }

    private static final class Json {
        static String write(Object value) {
            if (value == null) {
                return "null";
            }
            if (value instanceof String) {
                return quote((String) value);
            }
            if (value instanceof Number || value instanceof Boolean) {
                return String.valueOf(value);
            }
            if (value instanceof Map) {
                StringBuilder builder = new StringBuilder();
                builder.append('{');
                boolean first = true;
                for (Map.Entry<?, ?> entry : ((Map<?, ?>) value).entrySet()) {
                    if (!first) {
                        builder.append(',');
                    }
                    first = false;
                    builder.append(quote(String.valueOf(entry.getKey())));
                    builder.append(':');
                    builder.append(write(entry.getValue()));
                }
                builder.append('}');
                return builder.toString();
            }
            if (value instanceof Collection) {
                StringBuilder builder = new StringBuilder();
                builder.append('[');
                boolean first = true;
                for (Object item : (Collection<?>) value) {
                    if (!first) {
                        builder.append(',');
                    }
                    first = false;
                    builder.append(write(item));
                }
                builder.append(']');
                return builder.toString();
            }
            return quote(String.valueOf(value));
        }

        private static String quote(String value) {
            StringBuilder builder = new StringBuilder(value.length() + 16);
            builder.append('"');
            for (int i = 0; i < value.length(); i++) {
                char ch = value.charAt(i);
                switch (ch) {
                    case '"':
                        builder.append("\\\"");
                        break;
                    case '\\':
                        builder.append("\\\\");
                        break;
                    case '\n':
                        builder.append("\\n");
                        break;
                    case '\r':
                        builder.append("\\r");
                        break;
                    case '\t':
                        builder.append("\\t");
                        break;
                    default:
                        if (ch < 0x20) {
                            builder.append(String.format("\\u%04x", (int) ch));
                        } else {
                            builder.append(ch);
                        }
                }
            }
            builder.append('"');
            return builder.toString();
        }
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

    private static Map<String, String> readConfig(String configPath) throws IOException {
        if (configPath == null || configPath.trim().isEmpty()) {
            return Collections.emptyMap();
        }
        Path path = Paths.get(configPath);
        if (!Files.isRegularFile(path)) {
            return Collections.emptyMap();
        }
        Map<String, String> values = new LinkedHashMap<>();
        try (BufferedReader reader = Files.newBufferedReader(path, StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#") || !trimmed.contains("=")) {
                    continue;
                }
                int index = trimmed.indexOf('=');
                values.put(trimmed.substring(0, index).trim(),
                        trimmed.substring(index + 1).trim());
            }
        }
        return values;
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
