package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.ByteType;
import soot.CharType;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.ShortType;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThrowStmt;
import soot.tagkit.LineNumberTag;
import soot.tagkit.SourceLineNumberTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.UnitGraph;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
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

/**
 * Exception/variable-seeded static backward data-flow analysis.
 *
 * <p>The preferred analysis starts from a target exception in target.yaml and
 * discovers the throw value, exception payload, controlling guards, and their
 * data dependencies automatically.  The legacy seed variable list remains a
 * compatibility fallback.  Local Java/Jimple calls, discovered RPC
 * dispatches, interface dispatches, and explicitly enabled protocol bridges
 * all emit edges into the same static data-flow graph.</p>
 */
public final class CausynthPipeline {
    private static final Logger LOG = LoggerFactory.getLogger(CausynthPipeline.class);
    private static final String TRACE_RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";
    private static final String CONCOLIC_REGION_RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";

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
        if (!target.hasSeed()) {
            LOG.info("Seed backward analysis skipped: no seed_exception or seed_variables in {}",
                    target.specPath);
            return;
        }

        LOG.info("Seed backward analysis starts in {} mode from {}",
                target.seedMode(), target.seedDescription());
        AnalysisResult result = new SeedBackwardStaticAnalyzer(target).analyze();
        buildSymbolicExecutionPlan(result);
        buildSymbolicRegions(result);
        buildAutomaticDerivationBoundary(result);
        instrumentRuntimeTrace(result);
        instrumentConcolicRegions(result);
        boolean boundedOutputClosureCoverageReady =
                selectedBoundedOutputClosureCoverageReady(result);
        result.slices.put("boundedOutputClosureCoverageReady",
                boundedOutputClosureCoverageReady);
        result.slices.put("symbolicCoverageGateAuthority",
                boundedOutputClosureCoverageReady
                        ? "RUNTIME_SELECTED_BOUNDED_OUTPUT_CLOSURE_V1"
                        : "GLOBAL_SYMBOLIC_REGION_COVERAGE");
        new OutputWriter(target, result).writeAll();
        boolean strictCoverage = Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.coverage.strict"),
                System.getenv("CAUSYNTH_COVERAGE_STRICT"),
                "true"));
        if (strictCoverage
                && !Boolean.TRUE.equals(result.symbolicCoverage.get("complete"))
                && !boundedOutputClosureCoverageReady) {
            throw new IllegalStateException("Incomplete symbolic-region coverage: "
                    + result.symbolicCoverage);
        }
        if (strictCoverage
                && !Boolean.TRUE.equals(result.symbolicCoverage.get("complete"))) {
            LOG.info("Global symbolic-region coverage is incomplete, but the "
                            + "exact runtime-selected bounded output closure is "
                            + "ready; preserving strict coverage outside that "
                            + "selected activation");
        }
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
        RichTraceRefs richRefs = RichTraceRefs.create();
        ConcolicRegionRefs observationIsolation = Boolean.parseBoolean(
                firstNonBlank(
                        System.getProperty("causynth.instrument.concolic"),
                        System.getenv("CAUSYNTH_INSTRUMENT_CONCOLIC"),
                        "false")) ? ConcolicRegionRefs.create() : null;
        TraceFieldSelection traceFields = traceFieldSelection(result);
        TraceSiteSelection traceSites = traceSiteSelection(result);
        int count = 0;
        int fieldCount = 0;
        int richMethodCount = 0;
        int callSiteCount = 0;
        int branchCount = 0;
        for (Map<String, Object> methodRow : result.traceMethods) {
            String signature = String.valueOf(methodRow.get("method"));
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete() || method.isConstructor()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
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
                if (traceSites.relevantMethods.contains(signature)) {
                    RichInstrumentationStats stats = instrumentRichMethod(body, method,
                            originalUnits, insertionPoint, receiver, traceSites,
                            richRefs, observationIsolation);
                    richMethodCount++;
                    callSiteCount += stats.callSites;
                    branchCount += stats.branches;
                } else {
                    Stmt traceCall = Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(recordRef,
                                    StringConstant.v(signature), receiver));
                    List<Unit> traceUnits = new ArrayList<>();
                    beginTraceObservationIsolation(traceUnits,
                            observationIsolation);
                    traceUnits.add(traceCall);
                    endTraceObservationIsolation(traceUnits,
                            observationIsolation);
                    insertBeforeOrAppend(body, insertionPoint, traceUnits);
                }
                fieldCount += instrumentFieldTrace(body, method, recordFieldRef,
                        traceFields, originalUnits, observationIsolation);
                count++;
            } catch (RuntimeException exception) {
                LOG.debug("Skipping trace instrumentation for {}", signature, exception);
            }
        }
        result.slices.put("traceInstrumentedMethodCount", count);
        result.slices.put("traceInstrumentedFieldAccessCount", fieldCount);
        result.slices.put("richTraceInstrumentedMethodCount", richMethodCount);
        result.slices.put("traceInstrumentedCallSiteCount", callSiteCount);
        result.slices.put("traceInstrumentedBranchCount", branchCount);
        result.slices.put("traceObservationIsolatedFromConcolic",
                observationIsolation != null);
        LOG.info("Instrumented {} selected methods ({} rich), {} callsites, "
                        + "{} branches, and {} field accesses for runtime trace",
                count, richMethodCount, callSiteCount, branchCount, fieldCount);
    }

    /**
     * Inserts region hooks. Without an activation plan, static candidates are
     * retained for backward-compatible discovery runs. After concrete
     * discovery, the runtime activation plan is authoritative and a replay
     * transformation inserts hooks at the runtime-selected roots.
     */
    private void instrumentConcolicRegions(AnalysisResult result) {
        if (!Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                System.getenv("CAUSYNTH_INSTRUMENT_CONCOLIC"),
                "false"))) {
            return;
        }
        ConcolicRegionRefs refs = ConcolicRegionRefs.create();
        ConcolicBranchSelection branchSelection =
                ConcolicBranchSelection.from(result.symbolicRegions);
        ConcolicMaterializationSelection materializationSelection =
                concolicMaterializationSelection();
        ConcolicReplaySelection replaySelection = concolicReplaySelection();
        ConcolicOutputCaptureSelection outputCaptureSelection =
                concolicOutputCaptureSelection();
        Set<String> roots = concolicRootMethods(result);
        Set<String> backedViewMethods = concolicBackedViewMethods(result);
        backedViewMethods.addAll(roots);
        Set<String> taggedMethods = new LinkedHashSet<>(branchSelection.methods());
        taggedMethods.addAll(materializationSelection.localMethods());
        taggedMethods.addAll(materializationSelection.accessorCallerMethods());
        taggedMethods.addAll(replaySelection.methods());
        taggedMethods.addAll(outputCaptureSelection.methods());
        taggedMethods.addAll(backedViewMethods);
        for (String methodSignature : taggedMethods) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method != null && method.isConcrete()) {
                    tagOriginalUnits(snapshotUnits(method.retrieveActiveBody()));
                }
            } catch (RuntimeException ignored) {
            }
        }
        int instrumented = 0;
        int skipped = 0;
        for (String signature : roots) {
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete() || method.isConstructor()) {
                    skipped++;
                    continue;
                }
                Body body = method.retrieveActiveBody();
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                Unit insertionPoint = firstNonIdentity(body);
                Value receiver = NullConstant.v();
                if (!method.isStatic()) {
                    try {
                        receiver = body.getThisLocal();
                    } catch (RuntimeException ignored) {
                    }
                }
                Local token = newTraceLocal(body, LongType.v(),
                        "$causynthRegionToken");
                List<Unit> entry = new ArrayList<>();
                Unit tokenInitialization = Jimple.v().newAssignStmt(token,
                        LongConstant.v(0L));
                entry.add(tokenInitialization);
                ArrayType objectArrayType = ArrayType.v(
                        RefType.v("java.lang.Object"), 1);
                Local rootArguments = newTraceLocal(body, objectArrayType,
                        "$causynthRootArguments");
                entry.add(Jimple.v().newAssignStmt(rootArguments,
                        Jimple.v().newNewArrayExpr(
                                RefType.v("java.lang.Object"),
                                IntConstant.v(method.getParameterCount()))));
                for (int index = 0; index < method.getParameterCount(); index++) {
                    Type parameterType = method.getParameterType(index);
                    if (!(parameterType instanceof RefType)
                            && !(parameterType instanceof ArrayType)) {
                        // Primitive slots remain null by construction.  They
                        // are intentionally not root-selection predicates.
                        continue;
                    }
                    Value parameter;
                    try {
                        parameter = body.getParameterLocal(index);
                    } catch (RuntimeException ignored) {
                        continue;
                    }
                    entry.add(Jimple.v().newAssignStmt(
                            Jimple.v().newArrayRef(rootArguments,
                                    IntConstant.v(index)),
                            objectArg(body, parameter, entry)));
                }
                Unit enterRegion = Jimple.v().newAssignStmt(token,
                        Jimple.v().newStaticInvokeExpr(refs.enterRegion,
                                StringConstant.v(signature), receiver,
                                rootArguments));
                entry.add(enterRegion);
                for (int index = 0; index < method.getParameterCount(); index++) {
                    Value parameter;
                    try {
                        parameter = body.getParameterLocal(index);
                    } catch (RuntimeException ignored) {
                        continue;
                    }
                    Value primitiveValue = primitiveValueString(body,
                            parameter, entry);
                    if (PrimitiveWrapper.forType(parameter.getType()) != null) {
                        addPrimitiveArgumentMaterialization(body, parameter,
                                token, index, primitiveValue, entry,
                                refs.materializeArgument,
                                refs.pauseObservation,
                                refs.resumeObservation);
                    } else {
                        Value objectValue = objectArg(body, parameter, entry);
                        Local modeled = newTraceLocal(body,
                                RefType.v("java.lang.Object"),
                                "$causynthArgumentModel");
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.pauseObservation)));
                        entry.add(Jimple.v().newAssignStmt(modeled,
                                Jimple.v().newStaticInvokeExpr(
                                        refs.materializeArgument, token,
                                        IntConstant.v(index), objectValue,
                                        primitiveValue)));
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.resumeObservation)));
                        Value converted = parameter.getType() instanceof RefType
                                && "java.lang.Object".equals(((RefType)
                                parameter.getType()).getClassName())
                                ? modeled : Jimple.v().newCastExpr(modeled,
                                parameter.getType());
                        entry.add(Jimple.v().newAssignStmt(parameter,
                                converted));
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.pauseObservation)));
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.symbolizeArgument, token,
                                        IntConstant.v(index), parameter,
                                        primitiveValue)));
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.resumeObservation)));
                    }
                }
                // A JVM exception handler observes the locals state *before*
                // its protected instruction executes.  Starting the trap at
                // tokenInitialization therefore makes the category-2 token
                // Top at the handler and produces unverifiable bytecode when
                // throwRegion performs lload.  Start at enterRegion instead:
                // the zero token is then definitely assigned, while failures
                // in enterRegion and all later argument hooks remain covered.
                Unit regionStart = enterRegion;
                insertBeforeOrAppend(body, insertionPoint, entry);

                for (Unit unit : originalUnits) {
                    if (!(unit instanceof Stmt)) {
                        continue;
                    }
                    Stmt stmt = (Stmt) unit;
                    if (stmt instanceof ReturnStmt) {
                        insertRegionExit(body, stmt, ((ReturnStmt) stmt).getOp(),
                                token, refs.exitRegion, refs.pauseObservation,
                                refs.resumeObservation);
                    } else if (stmt instanceof ReturnVoidStmt) {
                        insertRegionExit(body, stmt, NullConstant.v(),
                                token, refs.exitRegion, refs.pauseObservation,
                                refs.resumeObservation);
                    }
                }
                // The cleanup trap must also cover enter/argument hooks.  If
                // a paused bookkeeping hook throws before the original first
                // statement, the token-specific handler still finishes the
                // context and releases the JVM-wide region owner.
                addRegionThrowHandler(body, regionStart, token,
                        refs.throwRegion,
                        refs.pauseObservation, refs.resumeObservation);
                instrumented++;
            } catch (RuntimeException exception) {
                skipped++;
                LOG.debug("Skipping concolic region root instrumentation for {}",
                signature, exception);
            }
        }
        int accessorCallContextCount =
                instrumentConcolicAccessorCallContexts(
                        materializationSelection, refs);
        int materializationCount = instrumentConcolicMaterializations(
                materializationSelection, refs);
        int replayMaterializationCount =
                instrumentConcolicReplayMaterializations(replaySelection, refs);
        int outputCaptureHookCount = instrumentConcolicOutputCaptures(
                outputCaptureSelection, refs);
        int backedViewMutationHookCount =
                instrumentConcolicBackedViewMutations(backedViewMethods, refs);
        int branchCount = instrumentConcolicBranches(branchSelection, refs);
        result.slices.put("concolicRegionRootCount", roots.size());
        result.slices.put("concolicRegionInstrumentedRootCount", instrumented);
        result.slices.put("concolicRegionSkippedRootCount", skipped);
        result.slices.put("concolicMappedBranchCount", branchCount);
        result.slices.put("concolicMaterializationHookCount",
                materializationCount);
        result.slices.put("concolicAccessorCallContextHookCount",
                accessorCallContextCount);
        result.slices.put("concolicReplayMaterializationHookCount",
                replayMaterializationCount);
        result.slices.put("concolicOutputCaptureHookCount",
                outputCaptureHookCount);
        result.slices.put("concolicBackedViewMutationHookCount",
                backedViewMutationHookCount);
        LOG.info("Instrumented {} symbolic-region roots for concolic replay ({} skipped)",
                instrumented, skipped);
    }

    private Set<String> concolicRootMethods(AnalysisResult result) {
        String planValue = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN")));
        if (!planValue.isEmpty()) {
            String selected = stringValue(firstNonBlank(
                    System.getProperty("causynth.concolic.activation.id"),
                    System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID")));
            try {
                Set<String> runtimeRoots = readRuntimeSelectedRoots(
                        Paths.get(planValue), selected);
                if (runtimeRoots.isEmpty()) {
                    throw new IllegalStateException(
                            "Activation plan contains no replayable runtime-selected roots: "
                                    + planValue);
                }
                result.slices.put("concolicRootAuthority",
                        "RUNTIME_ACTIVATION_PLAN");
                result.slices.put("concolicActivationPlan",
                        Paths.get(planValue).toAbsolutePath().toString());
                return runtimeRoots;
            } catch (IOException | RuntimeException exception) {
                throw new IllegalStateException(
                        "Could not load runtime-selected concolic roots from "
                                + planValue, exception);
            }
        }

        Set<String> staticCandidates = new LinkedHashSet<>();
        for (Map<String, Object> row : result.symbolicRegions) {
            String root = stringValue(firstNonBlank(
                    stringValue(row.get("staticRootCandidate")),
                    stringValue(row.get("rootMethod"))));
            if (!root.isEmpty()) {
                staticCandidates.add(root);
            }
        }
        result.slices.put("concolicRootAuthority", "STATIC_CANDIDATE_FALLBACK");
        return staticCandidates;
    }

    private ConcolicMaterializationSelection concolicMaterializationSelection() {
        String planValue = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN")));
        if (planValue.isEmpty()) {
            return new ConcolicMaterializationSelection();
        }
        String selected = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.id"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID")));
        try {
            return ConcolicMaterializationSelection.from(
                    Paths.get(planValue), selected);
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load concolic materializations from "
                            + planValue, exception);
        }
    }

    private ConcolicReplaySelection concolicReplaySelection() {
        String planValue = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN")));
        if (planValue.isEmpty()) {
            return new ConcolicReplaySelection();
        }
        String selected = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.id"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID")));
        try {
            return ConcolicReplaySelection.from(Paths.get(planValue), selected);
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load concolic replay materializations from "
                            + planValue, exception);
        }
    }

    private ConcolicOutputCaptureSelection concolicOutputCaptureSelection() {
        String planValue = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN")));
        if (planValue.isEmpty()) {
            return new ConcolicOutputCaptureSelection();
        }
        String selected = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.id"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID")));
        try {
            return ConcolicOutputCaptureSelection.from(Paths.get(planValue),
                    selected);
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load concolic output captures from "
                            + planValue, exception);
        }
    }

    static Set<String> readRuntimeSelectedRoots(Path activationPlan,
                                                String selectedActivation)
            throws IOException {
        if (activationPlan == null || !Files.isRegularFile(activationPlan)) {
            throw new IOException("Activation plan not found: " + activationPlan);
        }
        String selected = stringValue(firstNonBlank(selectedActivation));
        Set<String> roots = new LinkedHashSet<>();
        try (BufferedReader reader = Files.newBufferedReader(activationPlan,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonElement parsed = JsonParser.parseString(line);
                if (!parsed.isJsonObject()) {
                    continue;
                }
                JsonObject row = parsed.getAsJsonObject();
                String activationId = jsonString(row, "activationId");
                if (!selected.isEmpty()
                        && "ALL".equals(jsonString(row,
                        "activationSelectionRequired"))
                        && selected.equals(activationId)) {
                    throw new IOException("Activation " + selected
                            + " belongs to a reachability bundle that "
                            + "requires ALL plan rows");
                }
                if (!selected.isEmpty() && !selected.equals(activationId)) {
                    continue;
                }
                // Activation plans produced before the scheduler existed did
                // not carry an explicit readiness bit.  Preserve that format
                // while allowing the scheduler to be the authority for newer
                // plans.
                boolean ready = jsonBoolean(row, "symbolicReady", true)
                        || jsonBoolean(row, "schedulerReady", false);
                if (!jsonBoolean(row, "replayable", true) || !ready) {
                    continue;
                }
                String root = stringValue(firstNonBlank(
                        jsonString(row, "rootMethod"),
                        jsonString(row, "observedRootMethod")));
                if (!root.isEmpty()) {
                    roots.add(root);
                }
            }
        }
        return roots;
    }

    /**
     * Returns whether one exact scheduler-selected activation carries all of
     * the evidence needed to analyze only its bounded requested-output
     * closure.  This is deliberately stricter than root selection: older
     * discovery plans and branch-target plans must continue to require global
     * symbolic-region coverage.
     */
    static boolean selectedBoundedOutputClosureCoverageReady(
            Path activationPlan, String selectedActivation)
            throws IOException {
        if (activationPlan == null || !Files.isRegularFile(activationPlan)) {
            return false;
        }
        String selected = stringValue(firstNonBlank(selectedActivation));
        if (selected.isEmpty()) {
            return false;
        }

        JsonObject selectedRow = null;
        int selectedRowCount = 0;
        try (BufferedReader reader = Files.newBufferedReader(activationPlan,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonElement parsed;
                try {
                    parsed = JsonParser.parseString(line);
                } catch (RuntimeException malformed) {
                    return false;
                }
                if (!parsed.isJsonObject()) {
                    return false;
                }
                JsonObject row = parsed.getAsJsonObject();
                if (!selected.equals(jsonString(row, "activationId"))) {
                    continue;
                }
                selectedRowCount++;
                selectedRow = row;
            }
        }
        if (selectedRowCount != 1 || selectedRow == null) {
            return false;
        }
        return boundedOutputClosureRowReady(selectedRow, selected);
    }

    private boolean selectedBoundedOutputClosureCoverageReady(
            AnalysisResult result) {
        if (!Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                System.getenv("CAUSYNTH_INSTRUMENT_CONCOLIC"),
                "false"))) {
            return false;
        }
        String planValue = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN")));
        String selected = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.id"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID")));
        if (planValue.isEmpty() || selected.isEmpty()) {
            return false;
        }
        try {
            if (!selectedBoundedOutputClosureCoverageReady(
                    Paths.get(planValue), selected)) {
                return false;
            }
        } catch (IOException | RuntimeException unreadablePlan) {
            LOG.warn("Bounded output-closure coverage authority rejected "
                    + "activation plan {}", planValue, unreadablePlan);
            return false;
        }

        int rootCount = intValue(result.slices.get(
                "concolicRegionRootCount"), -1);
        int instrumentedCount = intValue(result.slices.get(
                "concolicRegionInstrumentedRootCount"), -1);
        int skippedCount = intValue(result.slices.get(
                "concolicRegionSkippedRootCount"), -1);
        String recordedPlan = stringValue(result.slices.get(
                "concolicActivationPlan"));
        boolean samePlan;
        try {
            samePlan = !recordedPlan.isEmpty()
                    && Paths.get(planValue).toAbsolutePath().normalize().equals(
                    Paths.get(recordedPlan).toAbsolutePath().normalize());
        } catch (RuntimeException invalidPath) {
            samePlan = false;
        }
        return "RUNTIME_ACTIVATION_PLAN".equals(stringValue(
                result.slices.get("concolicRootAuthority")))
                && samePlan
                && rootCount == 1
                && instrumentedCount == rootCount
                && skippedCount == 0;
    }

    private static boolean boundedOutputClosureRowReady(JsonObject row,
                                                        String selected) {
        JsonElement captureGoalElement = row.get("captureGoal");
        if (captureGoalElement == null || !captureGoalElement.isJsonObject()) {
            return false;
        }
        JsonObject captureGoal = captureGoalElement.getAsJsonObject();
        if (!"OUTPUT_CLOSURE".equals(jsonString(captureGoal, "kind"))
                || !"BOUNDED_OUTPUT_RELEVANT_PATHS".equals(
                jsonString(captureGoal, "scope"))
                || "TRANSITION_DISCOVERY_ONLY".equals(
                jsonString(captureGoal, "purpose"))) {
            return false;
        }

        String scheduleId = jsonString(row, "scheduleId");
        if (!selected.equals(jsonString(row, "activationId"))
                || !selected.equals(jsonString(row,
                "activationSelectionRequired"))
                || !selected.equals(jsonString(row,
                "activationBundleRootActivationId"))
                || scheduleId.isEmpty()
                || !scheduleId.equals(jsonString(row,
                "activationBundleScheduleId"))
                || !strictJsonIntEquals(row, "activationBundleSize", 1)
                || !strictJsonIntEquals(row, "activationBundleIndex", 0)
                || !"PRIMARY".equals(jsonString(row,
                "activationBundleMemberRole"))) {
            return false;
        }

        if (!strictJsonBooleanEquals(row, "replayable", true)
                || !strictJsonBooleanEquals(row, "boundaryReady", true)
                || !strictJsonBooleanEquals(row, "symbolicReady", true)
                || !strictJsonBooleanEquals(row, "schedulerReady", true)
                || !strictJsonBooleanEquals(row,
                "materializationComplete", true)
                || !strictJsonBooleanEquals(row,
                "runtimePathEvidenceComplete", true)
                || !strictJsonBooleanEquals(row,
                "requestedOutputSliceComplete", true)
                || !strictJsonBooleanEquals(row,
                "requestedOutputSliceRefinementComplete", true)
                || !strictJsonBooleanEquals(row,
                "requestedOutputCaptureComplete", true)
                || !strictJsonBooleanEquals(row,
                "branchOverrideProhibited", true)
                || !strictJsonBooleanEquals(row,
                "targetReplayRequired", false)
                || !strictJsonBooleanEquals(row,
                "pathSignatureTruncated", false)
                || !strictJsonBooleanEquals(row,
                "containedCallTreeTruncated", false)
                || !strictJsonIntEquals(row,
                "deferredMaterializationCount", 0)
                || !emptyJsonArray(row, "runtimeGaps")
                || !absentOrEmptyJsonArray(row, "forcedBranches")
                || !absentOrEmptyJsonArray(row, "replayMaterializations")
                || row.has("transitionDiscovery")
                || row.has("transitionOutputRefinement")) {
            return false;
        }
        boolean seedReplay = "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY"
                .equals(jsonString(row, "replayMode"))
                && "CAPTURE_OUTPUT_PATH".equals(jsonString(row,
                "executionPhase"))
                && absentOrEmptyJsonArray(row, "modelAssignments");
        boolean solverFlipReplay = solverOutputPathFlipReady(row, selected);
        if (!seedReplay && !solverFlipReplay) {
            return false;
        }

        JsonElement outputElement = row.get("requestedOutput");
        JsonElement sliceElement = row.get("requestedOutputSlice");
        if (outputElement == null || !outputElement.isJsonObject()
                || sliceElement == null || !sliceElement.isJsonObject()) {
            return false;
        }
        JsonObject output = outputElement.getAsJsonObject();
        JsonObject slice = sliceElement.getAsJsonObject();
        String outputPort = jsonString(output, "portId");
        String outputCell = jsonString(output, "cell");
        if (outputPort.isEmpty() || outputCell.isEmpty()
                || !outputPort.equals(jsonString(slice, "outputPort"))
                || !outputCell.equals(jsonString(slice, "outputCell"))
                || !strictJsonBooleanEquals(slice, "complete", true)
                || !strictJsonBooleanEquals(slice,
                "structuralComplete", true)
                || !strictJsonBooleanEquals(slice, "runtimeRefined", true)
                || !strictJsonBooleanEquals(slice,
                "runtimeRefinementComplete", true)
                || jsonString(slice, "runtimeRefinementAuthority").isEmpty()
                || !strictJsonBooleanEquals(slice,
                "unresolvedInputProvenanceComplete", true)
                || !strictJsonBooleanEquals(slice,
                "captureBindingsComplete", true)
                || !strictJsonBooleanEquals(slice,
                "methodBudgetTruncated", false)
                || !strictJsonBooleanEquals(slice,
                "causalCellBudgetTruncated", false)
                || !strictJsonBooleanEquals(slice,
                "regionTruncated", false)
                || !strictJsonBooleanEquals(slice, "truncated", false)) {
            return false;
        }
        if (!emptyJsonArray(slice, "unresolvedInputs")
                || !emptyJsonArray(slice, "unresolvedInputDetails")
                || !emptyJsonArray(slice, "truncationReasons")
                || !emptyJsonArray(slice, "captureBindingIssues")) {
            return false;
        }

        JsonElement outputs = row.get("outputs");
        int matchingOutputs = 0;
        if (outputs == null || !outputs.isJsonArray()) {
            return false;
        }
        for (JsonElement element : outputs.getAsJsonArray()) {
            if (element.isJsonObject()
                    && outputPort.equals(jsonString(element.getAsJsonObject(),
                    "symbol"))
                    && outputCell.equals(jsonString(element.getAsJsonObject(),
                    "cell"))) {
                matchingOutputs++;
            }
        }
        if (matchingOutputs != 1) {
            return false;
        }

        JsonElement captures = row.get("requestedOutputCapture");
        if (captures == null || !captures.isJsonArray()) {
            return false;
        }
        JsonElement captureRequiredElement = row.get(
                "requestedOutputCaptureRequired");
        if (captureRequiredElement == null
                || !captureRequiredElement.isJsonPrimitive()
                || !captureRequiredElement.getAsJsonPrimitive().isBoolean()) {
            return false;
        }
        boolean captureRequired = captureRequiredElement.getAsBoolean();
        if (captureRequired && captures.getAsJsonArray().size() == 0) {
            return false;
        }
        if (!captureRequired && captures.getAsJsonArray().size() != 0) {
            return false;
        }
        for (JsonElement element : captures.getAsJsonArray()) {
            if (!element.isJsonObject()
                    || !outputPort.equals(jsonString(element.getAsJsonObject(),
                    "outputPort"))
                    || !outputCell.equals(jsonString(element.getAsJsonObject(),
                    "outputCell"))
                    || jsonString(element.getAsJsonObject(),
                    "captureBindingId").isEmpty()) {
                return false;
            }
        }
        if (!strictJsonBooleanEquals(slice,
                "captureBindingsRequired", captureRequired)) {
            return false;
        }
        if (!captureRequired
                && !heapEffectCaptureDischargeReady(row, slice, outputPort,
                outputCell)) {
            return false;
        }
        return true;
    }

    /**
     * Admits the one non-seed replay shape that can soundly reuse a bounded
     * requested-output closure: an input-model-only Z3 path flip.  The model
     * may change concrete program inputs, but the branch remains an
     * observation target; no forced edge or reference-result injection is
     * authorized here.
     */
    private static boolean solverOutputPathFlipReady(JsonObject row,
                                                     String selected) {
        if (!selected.startsWith("ACT.PATH.")
                || !"RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY".equals(
                strictJsonString(row, "replayMode"))
                || !"REPLAY_OUTPUT_PATH_FLIP".equals(
                strictJsonString(row, "executionPhase"))
                || !absentOrStrictJsonBooleanEquals(row,
                "branchOverrideAllowed", false)) {
            return false;
        }

        String queryKey = strictJsonString(row, "pathQueryKey");
        String pathId = shortSha256(queryKey, 16);
        if (!queryKey.matches("[0-9a-f]{64}")
                || !selected.equals("ACT.PATH." + pathId)
                || !("SCHEDULE.PATH." + pathId).equals(
                strictJsonString(row, "scheduleId"))) {
            return false;
        }

        JsonElement assignmentsElement = row.get("modelAssignments");
        if (assignmentsElement == null || !assignmentsElement.isJsonArray()
                || assignmentsElement.getAsJsonArray().size() == 0) {
            return false;
        }
        Set<String> engineSymbols = new LinkedHashSet<>();
        Set<String> solverSymbols = new LinkedHashSet<>();
        for (JsonElement element : assignmentsElement.getAsJsonArray()) {
            if (!element.isJsonObject()
                    || !z3PathFlipAssignmentReady(element.getAsJsonObject(),
                    engineSymbols, solverSymbols)) {
                return false;
            }
        }

        JsonElement targetElement = row.get("targetBranch");
        if (targetElement == null || !targetElement.isJsonObject()) {
            return false;
        }
        JsonObject target = targetElement.getAsJsonObject();
        String targetSite = strictJsonString(target, "siteId");
        int targetOccurrence = strictJsonInt(target, "occurrence", -1);
        if (targetSite.isEmpty() || targetOccurrence <= 0
                || !strictJsonBooleanPresent(target, "desiredOutcome")
                || !strictJsonBooleanEquals(target, "validationOnly", true)
                || !strictJsonBooleanEquals(target,
                "branchOverrideAllowed", false)) {
            return false;
        }

        JsonElement prefixElement = row.get("expectedBranchPrefix");
        if (prefixElement == null || !prefixElement.isJsonArray()) {
            return false;
        }
        int previousConditionIndex = -1;
        Set<String> branchIdentities = new LinkedHashSet<>();
        for (JsonElement element : prefixElement.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                return false;
            }
            JsonObject expected = element.getAsJsonObject();
            String site = strictJsonString(expected, "siteId");
            int occurrence = strictJsonInt(expected, "occurrence", -1);
            int conditionIndex = strictJsonInt(expected,
                    "conditionIndex", -1);
            String identity = site + "\u0000" + occurrence;
            if (site.isEmpty() || occurrence <= 0 || conditionIndex < 0
                    || conditionIndex <= previousConditionIndex
                    || !strictJsonBooleanPresent(expected, "outcome")
                    || !branchIdentities.add(identity)
                    || targetSite.equals(site)
                    && targetOccurrence == occurrence) {
                return false;
            }
            previousConditionIndex = conditionIndex;
        }
        return true;
    }

    private static boolean z3PathFlipAssignmentReady(
            JsonObject assignment, Set<String> engineSymbols,
            Set<String> solverSymbols) {
        String engineSymbol = strictJsonString(assignment,
                "engineSymbol");
        String solverSymbol = strictJsonString(assignment,
                "solverSymbol");
        String inputSymbol = strictJsonString(assignment,
                "inputSymbol");
        String valueType = strictJsonString(assignment, "valueType");
        JsonElement value = assignment.get("value");
        JsonElement targetElement = assignment.get("target");
        if (engineSymbol.isEmpty() || solverSymbol.isEmpty()
                || inputSymbol.isEmpty()
                || !("BOOL".equals(valueType) || "INT".equals(valueType)
                || "REAL".equals(valueType)
                || "STRING".equals(valueType))
                || value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isString()
                || !"Z3_PATH_FLIP_MODEL".equals(strictJsonString(
                assignment, "authority"))
                || !strictJsonBooleanEquals(assignment,
                "materializeAtRealDefinition", true)
                || targetElement == null || !targetElement.isJsonObject()
                || !inputSymbol.equals(strictJsonString(
                targetElement.getAsJsonObject(), "symbol"))
                || !engineSymbols.add(engineSymbol)
                || !solverSymbols.add(solverSymbol)) {
            return false;
        }
        String modelValue = value.getAsString();
        return !"BOOL".equals(valueType)
                || "true".equals(modelValue) || "false".equals(modelValue);
    }

    private static String shortSha256(String value, int length) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(value.getBytes(
                    StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.substring(0, length);
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static boolean heapEffectCaptureDischargeReady(
            JsonObject row, JsonObject slice, String outputPort,
            String outputCell) {
        String inputPort = jsonString(slice, "captureDischargeInputPort");
        if (!strictJsonBooleanEquals(slice,
                "captureDischargedByHeapEffectTransformer", true)
                || !"HEAP_EFFECT_STATE_TRANSFORMER".equals(jsonString(slice,
                "captureDischargeAuthority"))
                || inputPort.isEmpty()
                || !outputPort.equals(jsonString(slice,
                "captureDischargeOutputPort"))
                || !outputCell.equals(jsonString(slice,
                "captureDischargeOutputCell"))
                || !strictJsonBooleanEquals(slice,
                "requestedStateTransformerContractApplicable", true)
                || !strictJsonBooleanEquals(slice,
                "requestedStateTransformerContractComplete", true)
                || !strictJsonIntEquals(slice,
                "requestedStateTransformerContractVersion", 1)
                || jsonString(slice,
                "requestedStateTransformerContractAuthority").isEmpty()
                || !outputPort.equals(jsonString(slice,
                "requestedStateTransformerContractOutputPort"))
                || !outputCell.equals(jsonString(slice,
                "requestedStateTransformerContractOutputCell"))
                || !emptyJsonArray(slice,
                "requestedStateTransformerContractIssues")) {
            return false;
        }

        JsonElement obligations = slice.get(
                "requestedStateTransformerObligations");
        int obligationCount = strictJsonInt(slice,
                "requestedStateTransformerObligationCount", -1);
        if (obligations == null || !obligations.isJsonArray()
                || obligationCount <= 0
                || obligations.getAsJsonArray().size() != obligationCount) {
            return false;
        }
        for (JsonElement element : obligations.getAsJsonArray()) {
            if (!element.isJsonObject()
                    || !outputCell.equals(jsonString(element.getAsJsonObject(),
                    "targetCell"))
                    || jsonString(element.getAsJsonObject(), "siteId").isEmpty()
                    || jsonString(element.getAsJsonObject(), "method").isEmpty()
                    || jsonString(element.getAsJsonObject(),
                    "authority").isEmpty()) {
                return false;
            }
        }

        JsonElement bindings = row.get("heapStateBindings");
        int matchingBindings = 0;
        if (bindings == null || !bindings.isJsonArray()) {
            return false;
        }
        for (JsonElement element : bindings.getAsJsonArray()) {
            if (element.isJsonObject()
                    && inputPort.equals(jsonString(element.getAsJsonObject(),
                    "inputPort"))
                    && outputPort.equals(jsonString(element.getAsJsonObject(),
                    "outputPort"))
                    && outputCell.equals(jsonString(element.getAsJsonObject(),
                    "cell"))) {
                matchingBindings++;
            }
        }
        return matchingBindings == 1;
    }

    private static String jsonString(JsonObject object, String field) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean jsonBoolean(JsonObject object, String field,
                                       boolean fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int jsonInt(JsonObject object, String field, int fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean strictJsonBooleanEquals(JsonObject object,
                                                   String field,
                                                   boolean expected) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                && value.getAsBoolean() == expected;
    }

    private static boolean strictJsonBooleanPresent(JsonObject object,
                                                    String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean();
    }

    private static boolean absentOrStrictJsonBooleanEquals(
            JsonObject object, String field, boolean expected) {
        return !object.has(field)
                || strictJsonBooleanEquals(object, field, expected);
    }

    private static String strictJsonString(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString() : "";
    }

    private static boolean strictJsonIntEquals(JsonObject object,
                                               String field, int expected) {
        return strictJsonInt(object, field, Integer.MIN_VALUE) == expected;
    }

    private static int strictJsonInt(JsonObject object, String field,
                                     int fallback) {
        JsonElement value = object.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            return fallback;
        }
        try {
            String encoded = value.getAsString();
            if (!encoded.matches("-?(0|[1-9][0-9]*)")) {
                return fallback;
            }
            return Integer.parseInt(encoded);
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    private static boolean emptyJsonArray(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonArray()
                && value.getAsJsonArray().size() == 0;
    }

    private static boolean absentOrEmptyJsonArray(JsonObject object,
                                                  String field) {
        JsonElement value = object.get(field);
        return value == null || (value.isJsonArray()
                && value.getAsJsonArray().size() == 0);
    }

    /**
     * Wraps only activation-selected accessor invocations with a tiny
     * thread-local runtime context. The exact-call trap covers the invocation
     * instruction alone; its rethrow remains inside any original enclosing
     * try range, preserving the application's handler semantics.
     */
    private int instrumentConcolicAccessorCallContexts(
            ConcolicMaterializationSelection selection,
            ConcolicRegionRefs refs) {
        int count = 0;
        for (AccessorCallTarget target : selection.accessorCalls()) {
            SootMethod method;
            Body body;
            try {
                method = Scene.v().getMethod(target.callerMethod);
                if (method == null || !method.isConcrete()
                        || method.isConstructor()) {
                    throw new IllegalStateException(
                            "ACCESSOR_CALLSITE_CALLER_NOT_CONCRETE: "
                                    + target.callSiteId);
                }
                body = method.retrieveActiveBody();
            } catch (RuntimeException failure) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_CALLER_UNAVAILABLE: "
                                + target.callSiteId, failure);
            }
            List<Unit> units = snapshotUnits(body);
            tagOriginalUnits(units);
            Stmt selected = null;
            for (Unit unit : units) {
                if (originalUnitIndex(unit) != target.callUnitIndex) {
                    continue;
                }
                if (selected != null || !(unit instanceof Stmt)) {
                    throw new IllegalStateException(
                            "ACCESSOR_CALLSITE_NOT_UNIQUE: "
                                    + target.callSiteId);
                }
                selected = (Stmt) unit;
            }
            if (selected == null || !selected.containsInvokeExpr()) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_INVOKE_NOT_FOUND: "
                                + target.callSiteId);
            }
            InvokeExpr invocation = selected.getInvokeExpr();
            if (!target.declaredCallee.equals(
                    invocation.getMethodRef().getSignature())) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_DECLARED_CALLEE_MISMATCH: "
                                + target.callSiteId + " expected "
                                + target.declaredCallee + " but found "
                                + invocation.getMethodRef().getSignature());
            }
            if (!(invocation instanceof InstanceInvokeExpr)
                    || "<init>".equals(invocation.getMethodRef().name())) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_REQUIRES_INSTANCE_RECEIVER: "
                                + target.callSiteId);
            }

            Local contextToken = newTraceLocal(body, LongType.v(),
                    "$causynthAccessorContextToken");
            List<Unit> before = new ArrayList<>();
            before.add(Jimple.v().newAssignStmt(contextToken,
                    LongConstant.v(0L)));
            Value receiver = objectArg(body,
                    ((InstanceInvokeExpr) invocation).getBase(), before);
            before.add(Jimple.v().newAssignStmt(contextToken,
                    Jimple.v().newStaticInvokeExpr(
                            refs.enterAccessorCallContext,
                            StringConstant.v(target.callerMethod),
                            IntConstant.v(target.callUnitIndex),
                            StringConstant.v(target.callSiteId),
                            StringConstant.v(target.declaredCallee),
                            receiver)));
            insertBeforeSequence(body, selected, before);

            Unit normalExit = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.exitAccessorCallContext, contextToken));
            Unit continuation = Jimple.v().newNopStmt();
            Unit skipHandler = Jimple.v().newGotoStmt(continuation);
            Local caught = newTraceLocal(body,
                    RefType.v("java.lang.Throwable"),
                    "$causynthAccessorThrown");
            Unit handler = Jimple.v().newIdentityStmt(caught,
                    Jimple.v().newCaughtExceptionRef());
            Unit exceptionalExit = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.exitAccessorCallContext, contextToken));
            Unit rethrow = Jimple.v().newThrowStmt(caught);
            insertAfterSequence(body, selected, Arrays.asList(normalExit,
                    skipHandler, handler, exceptionalExit, rethrow,
                    continuation));
            SootClass throwable = Scene.v().getSootClass(
                    "java.lang.Throwable");
            body.getTraps().addFirst(Jimple.v().newTrap(throwable, selected,
                    normalExit, handler));
            count++;
        }
        return count;
    }

    private int instrumentConcolicMaterializations(
            ConcolicMaterializationSelection selection,
            ConcolicRegionRefs refs) {
        if (selection.isEmpty()) {
            return 0;
        }
        int count = 0;
        List<SootClass> classes = new ArrayList<>();
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            classes.add(sootClass);
        }
        for (SootClass sootClass : classes) {
            for (SootMethod method : new ArrayList<>(sootClass.getMethods())) {
                if (!method.isConcrete()) {
                    continue;
                }
                Body body;
                try {
                    body = method.retrieveActiveBody();
                } catch (RuntimeException ignored) {
                    continue;
                }
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                for (Unit unit : originalUnits) {
                    if (!(unit instanceof Stmt)) {
                        continue;
                    }
                    Stmt stmt = (Stmt) unit;
                    int unitIndex = originalUnitIndex(unit);
                    Set<FieldRef> fields = Collections.newSetFromMap(
                            new IdentityHashMap<FieldRef, Boolean>());
                    if (stmt instanceof AssignStmt
                            && ((AssignStmt) stmt).getRightOp()
                            instanceof FieldRef) {
                        fields.add((FieldRef) ((AssignStmt) stmt)
                                .getRightOp());
                    }
                    for (ValueBox box : stmt.getUseBoxes()) {
                        if (box.getValue() instanceof FieldRef) {
                            fields.add((FieldRef) box.getValue());
                        }
                    }
                    for (FieldRef field : fields) {
                        SootFieldRef fieldRef = field.getFieldRef();
                        if (!selection.matches(method.getSignature(),
                                unitIndex, fieldRef)) {
                            continue;
                        }
                        if (field instanceof StaticFieldRef) {
                            throw new IllegalStateException(
                                    "STATIC_FIELD_MATERIALIZATION_UNSUPPORTED: "
                                            + fieldRef.getSignature()
                                            + " at " + method.getSignature()
                                            + "#u" + unitIndex);
                        }
                        if (!(field instanceof InstanceFieldRef)) {
                            throw new IllegalStateException(
                                    "UNKNOWN_FIELD_MATERIALIZATION_UNSUPPORTED: "
                                            + fieldRef.getSignature()
                                            + " at " + method.getSignature()
                                            + "#u" + unitIndex);
                        }
                        InstanceFieldRef instanceField =
                                (InstanceFieldRef) field;
                        if (fieldRef.type() instanceof ArrayType) {
                            instrumentConsumedArrayFieldRead(body, method,
                                    stmt, unitIndex, instanceField, refs);
                            count++;
                            continue;
                        }
                        List<Unit> before = new ArrayList<>();
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.pauseObservation)));
                        Value owner = objectArg(body, instanceField.getBase(),
                                before);
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.materializeField,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex), owner,
                                        StringConstant.v(fieldRef.getSignature()),
                                        StringConstant.v(fieldRef.name()))));
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.resumeObservation)));
                        insertBeforeSequence(body, stmt, before);
                        count++;
                    }

                    if (!(stmt instanceof AssignStmt)) {
                        continue;
                    }
                    Value left = ((AssignStmt) stmt).getLeftOp();
                    if (!(left instanceof Local)
                            || !selection.matches(method.getSignature(),
                            ((Local) left).getName(), unitIndex)) {
                        continue;
                    }
                    Local local = (Local) left;
                    List<Unit> after = new ArrayList<>();
                    if (local.getType() instanceof RefType
                            || local.getType() instanceof ArrayType) {
                        Local modeled = newTraceLocal(body,
                                RefType.v("java.lang.Object"),
                                "$causynthReferenceModel");
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.pauseObservation)));
                        after.add(Jimple.v().newAssignStmt(modeled,
                                Jimple.v().newStaticInvokeExpr(
                                        refs.materializeReference,
                                        StringConstant.v(method.getSignature()),
                                        StringConstant.v(local.getName()),
                                        local)));
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.resumeObservation)));
                        after.add(Jimple.v().newAssignStmt(local,
                                Jimple.v().newCastExpr(modeled,
                                        local.getType())));
                    } else {
                        addPrimitiveMaterialization(body, method, local, after,
                                refs.materializePrimitive,
                                refs.pauseObservation,
                                refs.resumeObservation);
                    }
                    if (!after.isEmpty()) {
                        insertAfterSequence(body, stmt, after);
                        count++;
                    }
                }
            }
        }
        return count;
    }

    /**
     * Splits an array-valued {@code getfield} around the runtime hooks without
     * ever evaluating the field twice.  The synthetic local is the JVM value
     * produced by the original field read; both the post hook and the original
     * statement consume that same local.  Consequently a concurrent putfield
     * after the read cannot change either the program value or the VM array
     * expression associated with it.
     */
    private static void instrumentConsumedArrayFieldRead(
            Body body, SootMethod method, Stmt stmt, int unitIndex,
            InstanceFieldRef field, ConcolicRegionRefs refs) {
        if (!(stmt instanceof AssignStmt)
                || ((AssignStmt) stmt).getRightOp() != field) {
            throw new IllegalStateException(
                    "ARRAY_FIELD_READ_SHAPE_UNSUPPORTED: "
                            + field.getFieldRef().getSignature() + " at "
                            + method.getSignature() + "#u" + unitIndex);
        }

        AssignStmt assignment = (AssignStmt) stmt;
        Local consumed = newTraceLocal(body, field.getType(),
                "$causynthConsumedArrayField");
        Unit exactGetField = Jimple.v().newAssignStmt(consumed, field);
        assignment.setRightOp(consumed);

        List<Unit> sequence = new ArrayList<>();
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
        Value owner = objectArg(body, field.getBase(), sequence);
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.prepareFieldMaterialization,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), owner,
                        StringConstant.v(field.getFieldRef().getSignature()),
                        StringConstant.v(field.getFieldRef().name()))));
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
        sequence.add(exactGetField);
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.materializeConsumedField,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), owner,
                        StringConstant.v(field.getFieldRef().getSignature()),
                        StringConstant.v(field.getFieldRef().name()),
                        consumed)));
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
        insertBeforeSequence(body, stmt, sequence);
    }

    /**
     * Exposes solver-derived reference results at exact Jimple sites.  The
     * transformer deliberately has no knowledge of the semantic theory that
     * produced the value (Map, protocol, collection, and so on); that
     * provenance remains in the activation plan.  The original assignment is
     * executed first so the VM can retain its expression, then the modeled
     * value is written back for ordinary Java control flow to consume.
     */
    private int instrumentConcolicReplayMaterializations(
            ConcolicReplaySelection selection, ConcolicRegionRefs refs) {
        int count = 0;
        for (ReplayTarget target : selection.targets()) {
            try {
                SootMethod method = Scene.v().getMethod(target.method);
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                Unit unit = originalUnit(body, target.unitIndex);
                if (!(unit instanceof AssignStmt)) {
                    continue;
                }
                AssignStmt assignment = (AssignStmt) unit;
                Value result = assignment.getLeftOp();
                Type resultType = result.getType();
                if (!(resultType instanceof RefType)
                        && !(resultType instanceof ArrayType)) {
                    continue;
                }

                List<Unit> after = new ArrayList<>();
                after.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
                Value concreteResult = objectArg(body, result, after);
                Local modeledResult = newTraceLocal(body,
                        RefType.v("java.lang.Object"), "$causynthReplayResult");
                after.add(Jimple.v().newAssignStmt(modeledResult,
                        Jimple.v().newStaticInvokeExpr(
                                refs.materializeReplayReferenceResult,
                                StringConstant.v(method.getSignature()),
                                IntConstant.v(target.unitIndex),
                                concreteResult)));
                after.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
                Value converted = modeledResult;
                if (!(resultType instanceof RefType)
                        || !"java.lang.Object".equals(
                        ((RefType) resultType).getClassName())) {
                    converted = Jimple.v().newCastExpr(modeledResult,
                            resultType);
                }
                after.add(Jimple.v().newAssignStmt(result, converted));
                insertAfterSequence(body, assignment, after);
                count++;
            } catch (RuntimeException exception) {
                LOG.debug("Skipping concolic replay materialization for {}#u{}",
                        target.method, target.unitIndex, exception);
            }
        }
        return count;
    }

    /** Captures the VM expression at an exact activation-authorized endpoint. */
    private int instrumentConcolicOutputCaptures(
            ConcolicOutputCaptureSelection selection,
            ConcolicRegionRefs refs) {
        int count = 0;
        for (OutputCaptureTarget target : selection.targets()) {
            try {
                SootMethod method = Scene.v().getMethod(
                        target.instrumentedMethod());
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                Unit unit = originalUnit(body, target.unitIndex);
                if (target.isFieldAssignmentRhs()) {
                    count += instrumentFieldAssignmentOutputCapture(body,
                            unit, target, refs);
                    continue;
                }
                if (!(unit instanceof Stmt)
                        || !((Stmt) unit).containsInvokeExpr()) {
                    continue;
                }
                Stmt stmt = (Stmt) unit;
                InvokeExpr invoke = stmt.getInvokeExpr();
                if (!target.calleeMethod.equals(
                        invoke.getMethodRef().getSignature())
                        || target.argumentIndex < 0
                        || target.argumentIndex >= invoke.getArgCount()) {
                    continue;
                }
                Value argument = invoke.getArg(target.argumentIndex);
                List<Unit> before = new ArrayList<>();
                // Box while symbolic propagation is still enabled.  The
                // custom JDK models Wrapper.valueOf and transfers the exact
                // primitive shadow expression to the wrapper object consumed
                // by the runtime expression API.
                Value objectValue = boxedCaptureValue(body, argument, before);
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.pauseObservation)));
                Value primitiveValue = primitiveValueString(body, argument,
                        before);
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.recordOutputCapture,
                                StringConstant.v(target.callerMethod),
                                IntConstant.v(target.unitIndex),
                                StringConstant.v(target.siteId),
                                StringConstant.v(target.calleeMethod),
                                IntConstant.v(target.argumentIndex),
                                StringConstant.v(target.outputPort),
                                StringConstant.v(target.outputCell),
                                StringConstant.v(target.captureBindingId),
                                IntConstant.v(target.occurrence),
                                objectValue, primitiveValue)));
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.resumeObservation)));
                insertBeforeSequence(body, stmt, before);
                count++;
            } catch (RuntimeException exception) {
                LOG.debug("Skipping {} concolic output capture for {}#u{}",
                        target.captureKind, target.instrumentedMethod(),
                        target.unitIndex, exception);
            }
        }
        return count;
    }

    /**
     * Captures the value written by one exact original instance-field
     * assignment.  A non-immediate RHS is evaluated once into a local and the
     * original write is rewritten to consume that local; evaluating the RHS
     * again after the write could duplicate calls or allocation side effects.
     * The runtime hook itself is inserted after the write, so a failing
     * {@code putfield} cannot produce a capture.
     */
    private int instrumentFieldAssignmentOutputCapture(
            Body body, Unit unit, OutputCaptureTarget target,
            ConcolicRegionRefs refs) {
        if (!(unit instanceof AssignStmt)) return 0;
        AssignStmt assignment = (AssignStmt) unit;
        if (!(assignment.getLeftOp() instanceof InstanceFieldRef)) return 0;
        InstanceFieldRef field = (InstanceFieldRef) assignment.getLeftOp();
        if (!target.fieldSignature.equals(
                field.getFieldRef().getSignature())) {
            return 0;
        }

        Value rhs = assignment.getRightOp();
        if (!(rhs instanceof Local) && !(rhs instanceof Constant)) {
            Local evaluated = newTraceLocal(body, rhs.getType(),
                    "$causynthAssignedRhs");
            Unit evaluateOnce = Jimple.v().newAssignStmt(evaluated, rhs);
            assignment.setRightOp(evaluated);
            insertBeforeSequence(body, assignment,
                    Collections.singletonList(evaluateOnce));
            rhs = evaluated;
        }

        List<Unit> after = new ArrayList<>();
        Local activeToken = newTraceLocal(body, LongType.v(),
                "$causynthActiveToken");
        after.add(Jimple.v().newAssignStmt(activeToken,
                Jimple.v().newStaticInvokeExpr(refs.activeToken)));
        Value owner = objectArg(body, field.getBase(), after);
        Value assignedValue = boxedCaptureValue(body, rhs, after);
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
        Value primitiveValue = primitiveValueString(body, rhs, after);
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.recordFieldAssignmentOutput,
                        activeToken,
                        StringConstant.v(target.instrumentedMethod()),
                        IntConstant.v(target.unitIndex),
                        StringConstant.v(target.siteId),
                        StringConstant.v(target.fieldSignature),
                        StringConstant.v(target.captureBindingId),
                        StringConstant.v(target.outputPort),
                        StringConstant.v(target.outputCell),
                        IntConstant.v(target.occurrence),
                        owner, assignedValue, primitiveValue)));
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
        insertAfterSequence(body, assignment, after);
        return 1;
    }

    /**
     * Instruments the Java collection-view protocol which implements
     * {@code Iterator.remove()} as a mutation of the backing map.  Static
     * analysis deliberately supplies a broad set of same-thread region
     * methods; the runtime's active activation and identity bindings decide
     * which concrete views actually belong to the selected heap state.
     */
    private int instrumentConcolicBackedViewMutations(
            Set<String> methods, ConcolicRegionRefs refs) {
        int count = 0;
        for (String signature : methods) {
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                List<Unit> units = snapshotUnits(body);
                tagOriginalUnits(units);
                for (Unit unit : units) {
                    if (!(unit instanceof Stmt)) {
                        continue;
                    }
                    Stmt stmt = (Stmt) unit;
                    if (!stmt.containsInvokeExpr()
                            || !(stmt.getInvokeExpr()
                            instanceof InstanceInvokeExpr)) {
                        continue;
                    }
                    InvokeExpr invoke = stmt.getInvokeExpr();
                    InstanceInvokeExpr instance = (InstanceInvokeExpr) invoke;
                    String name = invoke.getMethodRef().name();
                    int unitIndex = originalUnitIndex(unit);
                    if (unitIndex < 0 || invoke.getArgCount() != 0) {
                        continue;
                    }

                    List<Unit> after = new ArrayList<>();
                    after.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.pauseObservation)));
                    boolean recognized = false;
                    if (stmt instanceof AssignStmt
                            && isBackedMapViewFactory(name)) {
                        Value view = ((AssignStmt) stmt).getLeftOp();
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.registerMapView,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex),
                                        objectArg(body, instance.getBase(), after),
                                        objectArg(body, view, after),
                                        StringConstant.v(mapViewKind(name)))));
                        recognized = true;
                    } else if (stmt instanceof AssignStmt
                            && isIteratorFactory(name)) {
                        Value iterator = ((AssignStmt) stmt).getLeftOp();
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.registerMapViewIterator,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex),
                                        objectArg(body, instance.getBase(), after),
                                        objectArg(body, iterator, after))));
                        recognized = true;
                    } else if (stmt instanceof AssignStmt
                            && "next".equals(name)) {
                        Value element = ((AssignStmt) stmt).getLeftOp();
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.recordMapIteratorNext,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex),
                                        objectArg(body, instance.getBase(), after),
                                        objectArg(body, element, after))));
                        recognized = true;
                    } else if ("remove".equals(name)
                            && invoke.getMethodRef().returnType()
                            instanceof VoidType) {
                        // A post-call hook is reached only when remove()
                        // returns normally. IllegalStateException and other
                        // exceptional removals therefore cannot become
                        // applied heap effects.
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.recordMapIteratorRemove,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex),
                                        objectArg(body, instance.getBase(), after))));
                        recognized = true;
                    }
                    if (!recognized) {
                        continue;
                    }
                    after.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.resumeObservation)));
                    insertAfterSequence(body, stmt, after);
                    count++;
                }
            } catch (RuntimeException exception) {
                LOG.debug("Skipping backed-view concolic instrumentation for {}",
                        signature, exception);
            }
        }
        return count;
    }

    private static Set<String> concolicBackedViewMethods(
            AnalysisResult result) {
        Set<String> methods = new LinkedHashSet<>();
        for (Map<String, Object> region : result.symbolicRegions) {
            Object values = region.get("methods");
            if (!(values instanceof Collection)) {
                continue;
            }
            for (Object value : (Collection<?>) values) {
                String method = stringValue(value);
                if (!method.isEmpty()) {
                    methods.add(method);
                }
            }
        }
        return methods;
    }

    private static boolean isBackedMapViewFactory(String name) {
        return "entrySet".equals(name) || "keySet".equals(name)
                || "values".equals(name);
    }

    private static boolean isIteratorFactory(String name) {
        return "iterator".equals(name) || "listIterator".equals(name)
                || "descendingIterator".equals(name);
    }

    private static String mapViewKind(String name) {
        if ("entrySet".equals(name)) return "ENTRY_SET";
        if ("keySet".equals(name)) return "KEY_SET";
        if ("values".equals(name)) return "VALUES";
        return "UNKNOWN";
    }

    private static void addPrimitiveMaterialization(
            Body body, SootMethod method, Local local, List<Unit> units,
            SootMethodRef materializePrimitive,
            SootMethodRef pauseObservation,
            SootMethodRef resumeObservation) {
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(local.getType());
        if (wrapper == null) {
            return;
        }
        SootClass wrapperClass = Scene.v().getSootClass(wrapper.className);
        RefType wrapperType = RefType.v(wrapper.className);
        SootMethodRef valueOf = Scene.v().makeMethodRef(wrapperClass,
                "valueOf", Collections.singletonList(local.getType()),
                wrapperType, true);
        Local boxed = newTraceLocal(body, wrapperType, "$causynthBox");
        units.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newStaticInvokeExpr(valueOf, local)));
        Local materialized = newTraceLocal(body,
                RefType.v("java.lang.Object"), "$causynthMaterialized");
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(pauseObservation)));
        units.add(Jimple.v().newAssignStmt(materialized,
                Jimple.v().newStaticInvokeExpr(materializePrimitive,
                        StringConstant.v(method.getSignature()),
                        StringConstant.v(local.getName()), boxed)));
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(resumeObservation)));
        Local cast = newTraceLocal(body, wrapperType, "$causynthUnbox");
        units.add(Jimple.v().newAssignStmt(cast,
                Jimple.v().newCastExpr(materialized, wrapperType)));
        SootMethodRef unbox = Scene.v().makeMethodRef(wrapperClass,
                wrapper.unboxMethod, Collections.<Type>emptyList(),
                local.getType(), false);
        units.add(Jimple.v().newAssignStmt(local,
                Jimple.v().newVirtualInvokeExpr(cast, unbox)));
    }

    private static void addPrimitiveArgumentMaterialization(
            Body body, Value parameter, Local token, int argumentIndex,
            Value primitiveValue, List<Unit> units,
            SootMethodRef materializeArgument,
            SootMethodRef pauseObservation,
            SootMethodRef resumeObservation) {
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(
                parameter.getType());
        if (wrapper == null) return;
        SootClass wrapperClass = Scene.v().getSootClass(wrapper.className);
        RefType wrapperType = RefType.v(wrapper.className);
        SootMethodRef valueOf = Scene.v().makeMethodRef(wrapperClass,
                "valueOf", Collections.singletonList(parameter.getType()),
                wrapperType, true);
        Local boxed = newTraceLocal(body, wrapperType,
                "$causynthArgumentBox");
        units.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newStaticInvokeExpr(valueOf, parameter)));
        Local materialized = newTraceLocal(body,
                RefType.v("java.lang.Object"),
                "$causynthArgumentMaterialized");
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(pauseObservation)));
        units.add(Jimple.v().newAssignStmt(materialized,
                Jimple.v().newStaticInvokeExpr(materializeArgument, token,
                        IntConstant.v(argumentIndex), boxed,
                        primitiveValue)));
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(resumeObservation)));
        Local cast = newTraceLocal(body, wrapperType,
                "$causynthArgumentUnbox");
        units.add(Jimple.v().newAssignStmt(cast,
                Jimple.v().newCastExpr(materialized, wrapperType)));
        SootMethodRef unbox = Scene.v().makeMethodRef(wrapperClass,
                wrapper.unboxMethod, Collections.<Type>emptyList(),
                parameter.getType(), false);
        units.add(Jimple.v().newAssignStmt(parameter,
                Jimple.v().newVirtualInvokeExpr(cast, unbox)));
    }

    private static int originalUnitIndex(Unit unit) {
        for (Tag tag : unit.getTags()) {
            if (tag instanceof OriginalUnitIndexTag) {
                return ((OriginalUnitIndexTag) tag).index;
            }
        }
        return -1;
    }

    private int instrumentConcolicBranches(ConcolicBranchSelection selection,
                                           ConcolicRegionRefs refs) {
        int count = 0;
        for (String methodSignature : selection.methods()) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                for (Integer unitIndex : selection.units(methodSignature)) {
                    Unit unit = originalUnit(body, unitIndex);
                    if (!(unit instanceof IfStmt)) {
                        continue;
                    }
                    instrumentConcolicBranch(body, method, (IfStmt) unit,
                            unitIndex, refs);
                    count++;
                }
            } catch (RuntimeException exception) {
                LOG.debug("Skipping concolic branch instrumentation for {}",
                        methodSignature, exception);
            }
        }
        return count;
    }

    private void instrumentConcolicBranch(Body body, SootMethod method,
                                          IfStmt branch, int unitIndex,
                                          ConcolicRegionRefs refs) {
        String expression = branch.getCondition().toString();
        Unit previousTarget = branch.getTarget();
        Unit falseSuccessor = body.getUnits().getSuccOf(branch);
        if (falseSuccessor == null) {
            return;
        }

        Local decision = newTraceLocal(body, BooleanType.v(),
                "$causynthBranchDecision");
        Local prepared = newTraceLocal(body, LongType.v(),
                "$causynthPreparedBranch");
        Local vmEvent = newTraceLocal(body, LongType.v(),
                "$causynthVmBranchEvent");
        Local vmOccurrence = newTraceLocal(body, IntType.v(),
                "$causynthVmBranchOccurrence");

        // Prepare Java-side occurrence state while observation is paused, but
        // invoke the native marker directly from the transformed method.  On
        // the exact path that native call is the final invocation before the
        // original IfStmt, so runtime bookkeeping bytecodes cannot consume
        // its pending VM event.  A zero handle means no symbolic activation
        // is active, or the required exact-event API was rejected; in either
        // case the runtime records concrete replay or fails closed.
        Unit noMarkerPath = Jimple.v().newNopStmt();
        List<Unit> beforeBranch = new ArrayList<>();
        // This must be a direct native call.  A long/double/float compare is
        // lowered by Soot before this prefix and leaves an exact VM witness
        // for the following IfStmt.  Entering a Java helper before pausing
        // would execute helper branches that could consume that witness.
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseVmPathCondition)));
        beforeBranch.add(Jimple.v().newAssignStmt(prepared,
                Jimple.v().newStaticInvokeExpr(refs.prepareBranch,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(expression))));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                LongConstant.v(0L)));
        beforeBranch.add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(prepared, LongConstant.v(0L)),
                noMarkerPath));
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeVmPathCondition)));
        beforeBranch.add(Jimple.v().newAssignStmt(vmOccurrence,
                Jimple.v().newCastExpr(prepared, IntType.v())));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                Jimple.v().newStaticInvokeExpr(refs.markConcolicBranch,
                                StringConstant.v(method.getSignature() + "#u"
                                + unitIndex),
                        vmOccurrence)));
        Unit exactTransfer = Jimple.v().newGotoStmt(branch);
        beforeBranch.add(exactTransfer);
        beforeBranch.add(noMarkerPath);
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeVmPathCondition)));
        insertBeforeSequence(body, branch, beforeBranch);
        // UnitPatchingChain redirects pre-existing targets whenever another
        // unit is inserted before their anchor.  Restore this internal edge
        // after the full prefix exists; otherwise the exact path jumps back
        // to prepareBranch and can never execute the original condition.
        ((soot.jimple.GotoStmt) exactTransfer).setTarget(branch);

        List<Unit> falsePath = new ArrayList<>();
        falsePath.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
        falsePath.add(Jimple.v().newAssignStmt(decision,
                Jimple.v().newStaticInvokeExpr(refs.resolveBranch,
                        prepared, vmEvent,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), StringConstant.v(expression),
                        IntConstant.v(0))));
        falsePath.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
        falsePath.add(Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(decision, IntConstant.v(0)),
                previousTarget));
        insertAfterSequence(body, branch, falsePath);

        Unit trueEntry = Jimple.v().newNopStmt();
        Unit truePause = Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation));
        Unit trueResolve = Jimple.v().newAssignStmt(decision,
                Jimple.v().newStaticInvokeExpr(refs.resolveBranch,
                        prepared, vmEvent,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), StringConstant.v(expression),
                        IntConstant.v(1)));
        Unit trueResume = Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation));
        Unit takeTrue = Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(decision, IntConstant.v(0)),
                previousTarget);
        Unit takeFalse = Jimple.v().newGotoStmt(falseSuccessor);
        body.getUnits().add(trueEntry);
        body.getUnits().add(truePause);
        body.getUnits().add(trueResolve);
        body.getUnits().add(trueResume);
        body.getUnits().add(takeTrue);
        body.getUnits().add(takeFalse);
        branch.setTarget(trueEntry);
    }

    private static Unit originalUnit(Body body, int requestedIndex) {
        List<Unit> current = snapshotUnits(body);
        boolean hasAuthoritativeOriginalTags = false;
        for (Unit unit : current) {
            for (Tag tag : unit.getTags()) {
                if (tag instanceof OriginalUnitIndexTag) {
                    hasAuthoritativeOriginalTags = true;
                    if (((OriginalUnitIndexTag) tag).index
                            == requestedIndex) {
                        return unit;
                    }
                }
            }
        }
        // Once any pass has established the original-index namespace, an
        // untagged unit belongs to instrumentation inserted by that or a
        // later pass.  Positional fallback would then be unsound: it could
        // attach a concolic hook to a trace-recorder call which merely shifted
        // into the requested slot.
        if (hasAuthoritativeOriginalTags) {
            return null;
        }
        return requestedIndex >= 0 && requestedIndex < current.size()
                ? current.get(requestedIndex) : null;
    }

    private void insertRegionExit(Body body, Stmt returnUnit, Value returnValue,
                                  Local token,
                                  SootMethodRef exitRef,
                                  SootMethodRef pauseObservation,
                                  SootMethodRef resumeObservation) {
        List<Unit> units = new ArrayList<>();
        // Wrapper.valueOf must execute before observation is paused so the
        // custom VM can attach the primitive shadow expression.  The wrapper
        // is then stable while serialization and concrete string formatting
        // execute with path-condition recording disabled.
        Value objectValue = boxedCaptureValue(body, returnValue, units);
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(pauseObservation)));
        Value primitiveValue = primitiveValueString(body, returnValue, units);
        units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                exitRef, token, objectValue, primitiveValue)));
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(resumeObservation)));
        insertBeforeSequence(body, returnUnit, units);
    }

    private static List<Unit> snapshotUnits(Body body) {
        List<Unit> units = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            units.add(unit);
        }
        return units;
    }

    private static void tagOriginalUnits(List<Unit> units) {
        // Trace and concolic instrumentation may run in the same transform.
        // The first pass tags the complete pre-instrumentation snapshot.  If
        // a later pass sees any such tag, every untagged unit is necessarily
        // synthetic and must stay outside the original-index namespace.
        for (Unit unit : units) {
            for (Tag tag : unit.getTags()) {
                if (tag instanceof OriginalUnitIndexTag) {
                    return;
                }
            }
        }
        for (int index = 0; index < units.size(); index++) {
            Unit unit = units.get(index);
            unit.addTag(new OriginalUnitIndexTag(index));
        }
    }

    private static TraceSiteSelection traceSiteSelection(AnalysisResult result) {
        TraceSiteSelection selection = new TraceSiteSelection();
        for (Map<String, Object> row : result.symbolicPlan) {
            String method = stringValue(row.get("method"));
            if (!method.isEmpty()) {
                selection.relevantMethods.add(method);
            }
        }
        for (Map<String, Object> edge : result.edges) {
            String method = stringValue(edge.get("method"));
            int unitIndex = intValue(edge.get("unitIndex"), -1);
            if (method.isEmpty() || unitIndex < 0) {
                continue;
            }
            String invoke = stringValue(edge.get("invoke"));
            String transfer = stringValue(edge.get("transferKind"));
            if (!invoke.isEmpty()) {
                selection.add(selection.callUnits, method, unitIndex);
            }
            if ("GUARD".equals(transfer)) {
                selection.add(selection.branchUnits, method, unitIndex);
            }
        }
        return selection;
    }

    private RichInstrumentationStats instrumentRichMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Value receiver, TraceSiteSelection sites,
            RichTraceRefs refs, ConcolicRegionRefs observationIsolation) {
        RichInstrumentationStats stats = new RichInstrumentationStats();
        Local callId = newTraceLocal(body, LongType.v(), "$causynthCallId");
        List<Unit> entryUnits = new ArrayList<>();
        beginTraceObservationIsolation(entryUnits, observationIsolation);
        // Existing traps may be retargeted to the first inserted unit.  Give
        // the synthetic long a verifier-visible value before any injected
        // helper call can throw and flow into an original catch/finally path.
        entryUnits.add(Jimple.v().newAssignStmt(callId, LongConstant.v(0L)));
        entryUnits.add(Jimple.v().newAssignStmt(callId,
                Jimple.v().newStaticInvokeExpr(refs.enterMethod,
                        StringConstant.v(method.getSignature()), receiver)));
        for (int index = 0; index < method.getParameterCount(); index++) {
            Value parameter;
            try {
                parameter = body.getParameterLocal(index);
            } catch (RuntimeException ignored) {
                continue;
            }
            Value objectValue = objectArg(body, parameter, entryUnits);
            Value primitiveValue = primitiveValueString(body, parameter, entryUnits);
            entryUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    refs.recordMethodArgument,
                    callId,
                    IntConstant.v(index),
                    StringConstant.v(method.getParameterType(index).toString()),
                    objectValue,
                    primitiveValue)));
        }
        endTraceObservationIsolation(entryUnits, observationIsolation);
        insertBeforeOrAppend(body, insertionPoint, entryUnits);

        Set<Integer> callUnits = sites.units(sites.callUnits, method.getSignature());
        Set<Integer> branchUnits = sites.units(sites.branchUnits, method.getSignature());
        for (int unitIndex = 0; unitIndex < originalUnits.size(); unitIndex++) {
            Unit unit = originalUnits.get(unitIndex);
            if (!(unit instanceof Stmt)) {
                continue;
            }
            Stmt stmt = (Stmt) unit;
            if (callUnits.contains(unitIndex) && stmt.containsInvokeExpr()
                    && !isRecorderInvoke(stmt.getInvokeExpr())) {
                instrumentCallSite(body, method, stmt, unitIndex, callId,
                        refs, observationIsolation);
                stats.callSites++;
            }
            if (branchUnits.contains(unitIndex) && stmt instanceof IfStmt) {
                instrumentBranch(body, method, (IfStmt) stmt, unitIndex,
                        callId, refs, observationIsolation);
                stats.branches++;
            }
            if (stmt instanceof ReturnStmt) {
                insertMethodExit(body, stmt, ((ReturnStmt) stmt).getOp(),
                        refs.exitMethod, observationIsolation);
            } else if (stmt instanceof ReturnVoidStmt) {
                insertMethodExit(body, stmt, NullConstant.v(),
                        refs.exitMethod, observationIsolation);
            }
        }
        addActiveThrowHandler(body, insertionPoint, refs.throwMethod,
                observationIsolation == null ? null
                        : observationIsolation.pauseObservation,
                observationIsolation == null ? null
                        : observationIsolation.resumeObservation);
        return stats;
    }

    private void instrumentCallSite(Body body, SootMethod method, Stmt stmt,
                                    int unitIndex, Local ownerCallId,
                                    RichTraceRefs refs,
                                    ConcolicRegionRefs observationIsolation) {
        InvokeExpr invoke = stmt.getInvokeExpr();
        List<Unit> before = new ArrayList<>();
        beginTraceObservationIsolation(before, observationIsolation);
        Value receiver = NullConstant.v();
        if (invoke instanceof InstanceInvokeExpr
                && !"<init>".equals(invoke.getMethodRef().name())) {
            receiver = objectArg(body, ((InstanceInvokeExpr) invoke).getBase(), before);
        }
        Local invocationId = newTraceLocal(body, LongType.v(), "$causynthInvocation");
        before.add(Jimple.v().newAssignStmt(invocationId,
                Jimple.v().newStaticInvokeExpr(refs.beginCall,
                        ownerCallId,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(invoke.getMethodRef().getSignature()),
                        receiver)));
        for (int index = 0; index < invoke.getArgCount(); index++) {
            Value argument = invoke.getArg(index);
            Value objectValue = objectArg(body, argument, before);
            Value primitiveValue = primitiveValueString(body, argument, before);
            Type declaredType = index < invoke.getMethodRef().parameterTypes().size()
                    ? invoke.getMethodRef().parameterType(index) : argument.getType();
            before.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    refs.recordCallArgument,
                    invocationId,
                    IntConstant.v(index),
                    StringConstant.v(declaredType.toString()),
                    objectValue,
                    primitiveValue)));
        }
        endTraceObservationIsolation(before, observationIsolation);
        insertBeforeSequence(body, stmt, before);

        Value returnValue = NullConstant.v();
        if (stmt instanceof AssignStmt) {
            returnValue = ((AssignStmt) stmt).getLeftOp();
        }
        List<Unit> after = new ArrayList<>();
        beginTraceObservationIsolation(after, observationIsolation);
        Value returnObject = objectArg(body, returnValue, after);
        Value primitiveReturn = primitiveValueString(body, returnValue, after);
        after.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.endCall, invocationId, returnObject, primitiveReturn)));
        endTraceObservationIsolation(after, observationIsolation);
        insertAfterSequence(body, stmt, after);
    }

    private void instrumentBranch(Body body, SootMethod method, IfStmt branch,
                                  int unitIndex, Local callId,
                                  RichTraceRefs refs,
                                  ConcolicRegionRefs observationIsolation) {
        String expression = branch.getCondition().toString();
        Unit originalTarget = branch.getTarget();
        List<Unit> falsePath = new ArrayList<>();
        beginTraceObservationIsolation(falsePath, observationIsolation);
        Unit falseRecord = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.recordBranch,
                callId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex),
                StringConstant.v(expression),
                IntConstant.v(0)));
        falsePath.add(falseRecord);
        endTraceObservationIsolation(falsePath, observationIsolation);
        insertAfterSequence(body, branch, falsePath);

        Unit trueEntry = Jimple.v().newNopStmt();
        List<Unit> truePath = new ArrayList<>();
        truePath.add(trueEntry);
        beginTraceObservationIsolation(truePath, observationIsolation);
        Unit trueRecord = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.recordBranch,
                callId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex),
                StringConstant.v(expression),
                IntConstant.v(1)));
        truePath.add(trueRecord);
        endTraceObservationIsolation(truePath, observationIsolation);
        Unit resume = Jimple.v().newGotoStmt(originalTarget);
        truePath.add(resume);
        for (Unit unit : truePath) {
            body.getUnits().add(unit);
        }
        branch.setTarget(trueEntry);
    }

    private void insertMethodExit(Body body, Stmt returnUnit, Value returnValue,
                                  SootMethodRef exitRef,
                                  ConcolicRegionRefs observationIsolation) {
        List<Unit> units = new ArrayList<>();
        beginTraceObservationIsolation(units, observationIsolation);
        Value objectValue = objectArg(body, returnValue, units);
        Value primitiveValue = primitiveValueString(body, returnValue, units);
        units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                exitRef, objectValue, primitiveValue)));
        endTraceObservationIsolation(units, observationIsolation);
        insertBeforeSequence(body, returnUnit, units);
    }

    private static void beginTraceObservationIsolation(
            List<Unit> units, ConcolicRegionRefs isolation) {
        if (isolation != null) {
            units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    isolation.pauseObservation)));
        }
    }

    private static void endTraceObservationIsolation(
            List<Unit> units, ConcolicRegionRefs isolation) {
        if (isolation != null) {
            units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    isolation.resumeObservation)));
        }
    }

    private void addActiveThrowHandler(Body body, Unit start,
                                       SootMethodRef throwRef) {
        addActiveThrowHandler(body, start, throwRef, null, null);
    }

    private void addActiveThrowHandler(Body body, Unit start,
                                       SootMethodRef throwRef,
                                       SootMethodRef pauseObservation,
                                       SootMethodRef resumeObservation) {
        if (start == null) {
            return;
        }
        SootClass throwableClass = Scene.v().getSootClass("java.lang.Throwable");
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                "$causynthThrown");
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit pause = pauseObservation == null ? null
                : Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                pauseObservation));
        Unit record = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                throwRef, caught));
        Unit resume = resumeObservation == null ? null
                : Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                resumeObservation));
        Unit rethrow = Jimple.v().newThrowStmt(caught);
        body.getUnits().add(handler);
        if (pause != null) {
            body.getUnits().add(pause);
        }
        body.getUnits().add(record);
        if (resume != null) {
            body.getUnits().add(resume);
        }
        body.getUnits().add(rethrow);
        Trap trap = Jimple.v().newTrap(throwableClass, start, handler, handler);
        body.getTraps().add(trap);
    }

    /**
     * Region roots own the token returned by their own entry hook.  Using the
     * ambient ThreadLocal token here lets an unselected nested/recursive root
     * accidentally finish its selected caller's region.
     */
    private void addRegionThrowHandler(Body body, Unit start, Local token,
                                       SootMethodRef throwRef,
                                       SootMethodRef pauseObservation,
                                       SootMethodRef resumeObservation) {
        if (start == null) {
            return;
        }
        SootClass throwableClass = Scene.v().getSootClass("java.lang.Throwable");
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                "$causynthRegionThrown");
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit pause = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                pauseObservation));
        Unit record = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                throwRef, token, caught));
        Unit resume = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                resumeObservation));
        Unit rethrow = Jimple.v().newThrowStmt(caught);
        body.getUnits().add(handler);
        body.getUnits().add(pause);
        body.getUnits().add(record);
        body.getUnits().add(resume);
        body.getUnits().add(rethrow);
        body.getTraps().add(Jimple.v().newTrap(throwableClass, start, handler,
                handler));
    }

    private static boolean isRecorderInvoke(InvokeExpr invoke) {
        return invoke != null
                && TRACE_RECORDER_CLASS.equals(invoke.getMethodRef()
                .declaringClass().getName());
    }

    private static void insertBeforeOrAppend(Body body, Unit anchor,
                                             List<Unit> units) {
        if (anchor == null) {
            for (Unit unit : units) {
                body.getUnits().add(unit);
            }
            return;
        }
        insertBeforeSequence(body, anchor, units);
    }

    private static void insertBeforeSequence(Body body, Unit anchor,
                                             List<Unit> units) {
        for (Unit unit : units) {
            body.getUnits().insertBefore(unit, anchor);
        }
    }

    private static void insertAfterSequence(Body body, Unit anchor,
                                            List<Unit> units) {
        Unit current = anchor;
        for (Unit unit : units) {
            body.getUnits().insertAfter(unit, current);
            current = unit;
        }
    }

    private int instrumentFieldTrace(Body body, SootMethod method,
                                     SootMethodRef recordFieldRef,
                                     TraceFieldSelection traceFields,
                                     List<Unit> units,
                                     ConcolicRegionRefs observationIsolation) {
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
        for (int unitIndex = 0; unitIndex < units.size(); unitIndex++) {
            Unit unit = units.get(unitIndex);
            if (!(unit instanceof Stmt)) {
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
                            methodReceiver, right, true, traceFields,
                            observationIsolation);
                }
                if (right instanceof InstanceFieldRef) {
                    count += insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                            method.getSignature(), unitIndex, (InstanceFieldRef) right,
                            methodReceiver, left, true, traceFields,
                            observationIsolation);
                }
            } else {
                for (ValueBox box : stmt.getUseBoxes()) {
                    Value value = box.getValue();
                    if (value instanceof InstanceFieldRef) {
                        count += insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                                method.getSignature(), unitIndex, (InstanceFieldRef) value,
                                methodReceiver, value, false, traceFields,
                                observationIsolation);
                    }
                }
            }
        }
        return count;
    }

    private int insertFieldTrace(Body body, Unit unit, SootMethodRef recordFieldRef,
                                 String kind, String method, int unitIndex,
                                 InstanceFieldRef fieldRef, Value methodReceiverValue,
                                 Value value,
                                 boolean fieldValueIsReadValue,
                                 TraceFieldSelection traceFields,
                                 ConcolicRegionRefs observationIsolation) {
        String field = fieldRef.getFieldRef().getSignature();
        if (!shouldInstrumentField(field, traceFields)) {
            return 0;
        }
        List<Unit> prefixUnits = new ArrayList<>();
        beginTraceObservationIsolation(prefixUnits, observationIsolation);
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
        prefixUnits.add(traceCall);
        endTraceObservationIsolation(prefixUnits, observationIsolation);
        if (fieldValueIsReadValue || "FIELD_WRITE".equals(kind)) {
            insertAfterSequence(body, unit, prefixUnits);
        } else {
            insertBeforeSequence(body, unit, prefixUnits);
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

    /** Returns the exact assigned value as an Object, boxing primitives. */
    private static Value boxedCaptureValue(Body body, Value value,
                                           List<Unit> prefixUnits) {
        if (value == null || value instanceof NullConstant) {
            return NullConstant.v();
        }
        if (value.getType() instanceof RefType
                || value.getType() instanceof ArrayType) {
            return immediateValue(body, value, prefixUnits);
        }
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(value.getType());
        if (wrapper == null) return NullConstant.v();
        SootClass wrapperClass = Scene.v().getSootClass(wrapper.className);
        RefType wrapperType = RefType.v(wrapper.className);
        SootMethodRef valueOf = Scene.v().makeMethodRef(wrapperClass,
                "valueOf", Collections.singletonList(value.getType()),
                wrapperType, true);
        Value source = immediateValue(body, value, prefixUnits);
        Local boxed = newTraceLocal(body, wrapperType,
                "$causynthCaptureBox");
        prefixUnits.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newStaticInvokeExpr(valueOf, source)));
        return boxed;
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

    private static SootClass traceRecorderClass() {
        SootClass recorder = Scene.v().getSootClassUnsafe(TRACE_RECORDER_CLASS);
        if (recorder == null) {
            recorder = new SootClass(TRACE_RECORDER_CLASS, Modifier.PUBLIC);
            recorder.setPhantomClass();
            Scene.v().addClass(recorder);
        }
        return recorder;
    }

    private static final class RichTraceRefs {
        private final SootMethodRef enterMethod;
        private final SootMethodRef recordMethodArgument;
        private final SootMethodRef beginCall;
        private final SootMethodRef recordCallArgument;
        private final SootMethodRef endCall;
        private final SootMethodRef recordBranch;
        private final SootMethodRef exitMethod;
        private final SootMethodRef throwMethod;

        private RichTraceRefs(SootMethodRef enterMethod,
                              SootMethodRef recordMethodArgument,
                              SootMethodRef beginCall,
                              SootMethodRef recordCallArgument,
                              SootMethodRef endCall,
                              SootMethodRef recordBranch,
                              SootMethodRef exitMethod,
                              SootMethodRef throwMethod) {
            this.enterMethod = enterMethod;
            this.recordMethodArgument = recordMethodArgument;
            this.beginCall = beginCall;
            this.recordCallArgument = recordCallArgument;
            this.endCall = endCall;
            this.recordBranch = recordBranch;
            this.exitMethod = exitMethod;
            this.throwMethod = throwMethod;
        }

        private static RichTraceRefs create() {
            SootClass recorder = traceRecorderClass();
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            return new RichTraceRefs(
                    Scene.v().makeMethodRef(recorder, "enterMethod",
                            Arrays.asList(string, object), LongType.v(), true),
                    Scene.v().makeMethodRef(recorder, "recordMethodArgument",
                            Arrays.asList(LongType.v(), IntType.v(), string,
                                    object, string), VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "beginCall",
                            Arrays.asList(LongType.v(), string, IntType.v(),
                                    string, object), LongType.v(), true),
                    Scene.v().makeMethodRef(recorder, "recordCallArgument",
                            Arrays.asList(LongType.v(), IntType.v(), string,
                                    object, string), VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "endCall",
                            Arrays.asList(LongType.v(), object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "recordBranch",
                            Arrays.asList(LongType.v(), string, IntType.v(),
                                    string, BooleanType.v()), VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "exitActiveMethod",
                            Arrays.asList(object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "throwActiveMethod",
                            Collections.singletonList(
                                    RefType.v("java.lang.Throwable")),
                            VoidType.v(), true));
        }
    }

    private static final class ConcolicRegionRefs {
        private final SootMethodRef enterRegion;
        private final SootMethodRef enterAccessorCallContext;
        private final SootMethodRef exitAccessorCallContext;
        private final SootMethodRef materializeArgument;
        private final SootMethodRef symbolizeArgument;
        private final SootMethodRef materializeReference;
        private final SootMethodRef materializePrimitive;
        private final SootMethodRef materializeField;
        private final SootMethodRef prepareFieldMaterialization;
        private final SootMethodRef materializeConsumedField;
        private final SootMethodRef materializeReplayReferenceResult;
        private final SootMethodRef registerMapView;
        private final SootMethodRef registerMapViewIterator;
        private final SootMethodRef recordMapIteratorNext;
        private final SootMethodRef recordMapIteratorRemove;
        private final SootMethodRef recordOutputCapture;
        private final SootMethodRef activeToken;
        private final SootMethodRef recordFieldAssignmentOutput;
        private final SootMethodRef pauseObservation;
        private final SootMethodRef resumeObservation;
        private final SootMethodRef pauseVmPathCondition;
        private final SootMethodRef resumeVmPathCondition;
        private final SootMethodRef prepareBranch;
        private final SootMethodRef markConcolicBranch;
        private final SootMethodRef resolveBranch;
        private final SootMethodRef exitRegion;
        private final SootMethodRef throwRegion;

        private ConcolicRegionRefs(SootMethodRef enterRegion,
                                   SootMethodRef enterAccessorCallContext,
                                   SootMethodRef exitAccessorCallContext,
                                   SootMethodRef materializeArgument,
                                   SootMethodRef symbolizeArgument,
                                   SootMethodRef materializeReference,
                                   SootMethodRef materializePrimitive,
                                   SootMethodRef materializeField,
                                   SootMethodRef prepareFieldMaterialization,
                                   SootMethodRef materializeConsumedField,
                                   SootMethodRef materializeReplayReferenceResult,
                                   SootMethodRef registerMapView,
                                   SootMethodRef registerMapViewIterator,
                                   SootMethodRef recordMapIteratorNext,
                                   SootMethodRef recordMapIteratorRemove,
                                   SootMethodRef recordOutputCapture,
                                   SootMethodRef activeToken,
                                   SootMethodRef recordFieldAssignmentOutput,
                                   SootMethodRef pauseObservation,
                                   SootMethodRef resumeObservation,
                                   SootMethodRef pauseVmPathCondition,
                                   SootMethodRef resumeVmPathCondition,
                                   SootMethodRef prepareBranch,
                                   SootMethodRef markConcolicBranch,
                                   SootMethodRef resolveBranch,
                                   SootMethodRef exitRegion,
                                   SootMethodRef throwRegion) {
            this.enterRegion = enterRegion;
            this.enterAccessorCallContext = enterAccessorCallContext;
            this.exitAccessorCallContext = exitAccessorCallContext;
            this.materializeArgument = materializeArgument;
            this.symbolizeArgument = symbolizeArgument;
            this.materializeReference = materializeReference;
            this.materializePrimitive = materializePrimitive;
            this.materializeField = materializeField;
            this.prepareFieldMaterialization = prepareFieldMaterialization;
            this.materializeConsumedField = materializeConsumedField;
            this.materializeReplayReferenceResult =
                    materializeReplayReferenceResult;
            this.registerMapView = registerMapView;
            this.registerMapViewIterator = registerMapViewIterator;
            this.recordMapIteratorNext = recordMapIteratorNext;
            this.recordMapIteratorRemove = recordMapIteratorRemove;
            this.recordOutputCapture = recordOutputCapture;
            this.activeToken = activeToken;
            this.recordFieldAssignmentOutput =
                    recordFieldAssignmentOutput;
            this.pauseObservation = pauseObservation;
            this.resumeObservation = resumeObservation;
            this.pauseVmPathCondition = pauseVmPathCondition;
            this.resumeVmPathCondition = resumeVmPathCondition;
            this.prepareBranch = prepareBranch;
            this.markConcolicBranch = markConcolicBranch;
            this.resolveBranch = resolveBranch;
            this.exitRegion = exitRegion;
            this.throwRegion = throwRegion;
        }

        private static ConcolicRegionRefs create() {
            SootClass runtime = Scene.v().getSootClassUnsafe(
                    CONCOLIC_REGION_RUNTIME_CLASS);
            if (runtime == null) {
                runtime = new SootClass(CONCOLIC_REGION_RUNTIME_CLASS,
                        Modifier.PUBLIC);
                runtime.setPhantomClass();
                Scene.v().addClass(runtime);
            }
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            SootClass system = Scene.v().getSootClassUnsafe(
                    "java.lang.System");
            if (system == null) {
                system = new SootClass("java.lang.System", Modifier.PUBLIC);
                system.setPhantomClass();
                Scene.v().addClass(system);
            }
            return new ConcolicRegionRefs(
                    Scene.v().makeMethodRef(runtime, "enterRegion",
                            Arrays.asList(string, object,
                                    ArrayType.v(object, 1)),
                            LongType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "enterAccessorCallContext",
                            Arrays.asList(string, IntType.v(), string,
                                    string, object), LongType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "exitAccessorCallContext",
                            Collections.<Type>singletonList(LongType.v()),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "materializeArgument",
                            Arrays.asList(LongType.v(), IntType.v(), object,
                                    string), object, true),
                    Scene.v().makeMethodRef(runtime, "symbolizeArgument",
                            Arrays.asList(LongType.v(), IntType.v(), object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "materializeReference",
                            Arrays.asList(string, string, object),
                            object, true),
                    Scene.v().makeMethodRef(runtime, "materializePrimitive",
                            Arrays.asList(string, string, object),
                            object, true),
                    Scene.v().makeMethodRef(runtime, "materializeField",
                            Arrays.asList(string, IntType.v(), object, string,
                                    string), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "prepareFieldMaterialization",
                            Arrays.asList(string, IntType.v(), object, string,
                                    string), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "materializeConsumedField",
                            Arrays.asList(string, IntType.v(), object, string,
                                    string, object), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "materializeReplayReferenceResult",
                            Arrays.asList(string, IntType.v(), object),
                            object, true),
                    Scene.v().makeMethodRef(runtime, "registerMapView",
                            Arrays.asList(string, IntType.v(), object, object,
                                    string), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "registerMapViewIterator",
                            Arrays.asList(string, IntType.v(), object, object),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "recordMapIteratorNext",
                            Arrays.asList(string, IntType.v(), object, object),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "recordMapIteratorRemove",
                            Arrays.asList(string, IntType.v(), object),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "recordOutputCapture",
                            Arrays.asList(string, IntType.v(), string, string,
                                    IntType.v(), string, string, string,
                                    IntType.v(), object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "activeToken",
                            Collections.<Type>emptyList(), LongType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "recordFieldAssignmentOutput",
                            Arrays.asList(LongType.v(), string, IntType.v(),
                                    string, string, string, string, string,
                                    IntType.v(), object, object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "pauseObservation",
                            Collections.<Type>emptyList(), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "resumeObservation",
                            Collections.<Type>emptyList(), VoidType.v(), true),
                    Scene.v().makeMethodRef(system,
                            "pauseConcolicPathCondition",
                            Collections.<Type>emptyList(), VoidType.v(), true),
                    Scene.v().makeMethodRef(system,
                            "resumeConcolicPathCondition",
                            Collections.<Type>emptyList(), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "prepareBranch",
                            Arrays.asList(string, IntType.v(), string),
                            LongType.v(), true),
                    Scene.v().makeMethodRef(system, "markConcolicBranch",
                            Arrays.asList(string, IntType.v()),
                            LongType.v(), true),
                    Scene.v().makeMethodRef(runtime, "resolveBranch",
                            Arrays.asList(LongType.v(), LongType.v(), string,
                                    IntType.v(), string,
                                    BooleanType.v()), BooleanType.v(), true),
                    Scene.v().makeMethodRef(runtime, "exitRegion",
                            Arrays.asList(LongType.v(), object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "throwRegion",
                            Arrays.asList(LongType.v(),
                                    RefType.v("java.lang.Throwable")),
                            VoidType.v(), true));
        }
    }

    private static final class ConcolicBranchSelection {
        private final Map<String, Set<Integer>> unitsByMethod =
                new LinkedHashMap<>();

        private static ConcolicBranchSelection from(
                List<Map<String, Object>> regions) {
            ConcolicBranchSelection result = new ConcolicBranchSelection();
            for (Map<String, Object> region : regions) {
                Object value = region.get("branchPolicies");
                if (!(value instanceof Collection)) {
                    continue;
                }
                for (Object item : (Collection<?>) value) {
                    if (!(item instanceof Map)) {
                        continue;
                    }
                    Map<?, ?> policy = (Map<?, ?>) item;
                    String method = stringValue(policy.get("method"));
                    int unit = intValue(policy.get("unitIndex"), -1);
                    if (!method.isEmpty() && unit >= 0) {
                        result.unitsByMethod.computeIfAbsent(method,
                                ignored -> new LinkedHashSet<>()).add(unit);
                    }
                }
            }
            return result;
        }

        private Set<String> methods() {
            return unitsByMethod.keySet();
        }

        private Set<Integer> units(String method) {
            Set<Integer> units = unitsByMethod.get(method);
            return units == null ? Collections.emptySet() : units;
        }
    }

    /**
     * Resolves the concrete field selected for a heap materialization hook.
     * Runtime field evidence is authoritative when available.  A cell such as
     * {@code <Owner: T method()>.return#field:x} names a projection from a
     * method result; {@code Owner} does not declare {@code x} and must not be
     * reused as the Soot field owner.
     */
    static String[] resolveConcolicFieldTarget(JsonObject action) {
        String cell = jsonString(action, "cell");
        String owner = jsonString(action, "accessOwnerClass");
        String name = jsonString(action, "accessField");
        JsonElement path = action.get("fieldPath");
        if (name.isEmpty() && path != null && path.isJsonArray()
                && path.getAsJsonArray().size() > 0) {
            name = path.getAsJsonArray().get(0).getAsString();
        }

        Matcher observed = ConcolicMaterializationSelection.FIELD.matcher(
                jsonString(action, "field"));
        if (observed.matches() && !isMethodMember(observed.group(3))) {
            owner = firstNonBlank(owner, observed.group(1));
            name = firstNonBlank(name, observed.group(3));
        }

        Matcher declared = ConcolicMaterializationSelection.FIELD.matcher(cell);
        if (declared.matches() && !isMethodMember(declared.group(3))) {
            owner = firstNonBlank(owner, declared.group(1));
            name = firstNonBlank(name, declared.group(3));
        } else {
            name = firstNonBlank(name,
                    ConcolicMaterializationSelection.projectedField(cell),
                    ConcolicMaterializationSelection.projectedField(
                            jsonString(action, "field")));
        }
        String normalizedOwner = firstNonBlank(owner);
        String normalizedName = firstNonBlank(name);
        return new String[]{normalizedOwner == null ? "" : normalizedOwner,
                normalizedName == null ? "" : normalizedName};
    }

    private static boolean isMethodMember(String member) {
        return member != null && member.indexOf('(') >= 0;
    }

    /**
     * The small set of concrete Jimple values that a scheduled activation
     * asks Soot to expose to the VM.  This is intentionally activation-plan
     * driven: the static region supplies candidates, while the runtime
     * instance decides which concrete local/heap owner is authoritative.
     */
    private static final class ConcolicMaterializationSelection {
        private static final Pattern LOCAL = Pattern.compile(
                "^(<.+>)::([^#]+)(?:#.*)?$");
        private static final Pattern FIELD = Pattern.compile(
                "^<([^:]+):\\s+(.+)\\s+([^\\s>]+)>(?:#field:([^#]+))?.*$");
        private static final String CONSUMED_SITE_AUTHORITY =
                "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                        + "OWNER_WITHIN_REGION_INSTANCE_V1";
        private static final String CONSUMED_OCCURRENCE_AUTHORITY =
                "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1";
        private static final String DIRECT_ROOT_AUTHORITY =
                "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1";
        private static final String ARGUMENT_ROOT_AUTHORITY =
                "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                        + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
        private static final String RECEIVER_ROOT_AUTHORITY =
                "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_"
                        + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
        private static final String LOCAL_ROOT_AUTHORITY =
                "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_AND_"
                        + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
        private static final String ACCESSOR_CALLSITE_AUTHORITY =
                "STATIC_UNIQUE_EXACT_DECLARED_FIELD_ACCESSOR_CALLSITE_V1";

        private final Map<String, Map<String, Set<Integer>>> localsByMethod =
                new LinkedHashMap<>();
        private final List<FieldTarget> fields = new ArrayList<>();
        private final Map<String, AccessorCallTarget> accessorCallsBySite =
                new LinkedHashMap<>();
        private final List<String> unsupported = new ArrayList<>();

        private static ConcolicMaterializationSelection from(
                Path activationPlan, String selectedActivation)
                throws IOException {
            if (activationPlan == null || !Files.isRegularFile(activationPlan)) {
                throw new IOException("Activation plan not found: "
                        + activationPlan);
            }
            ConcolicMaterializationSelection result =
                    new ConcolicMaterializationSelection();
            String selected = stringValue(firstNonBlank(selectedActivation));
            try (BufferedReader reader = Files.newBufferedReader(activationPlan,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) {
                        continue;
                    }
                    JsonElement parsed = JsonParser.parseString(line);
                    if (!parsed.isJsonObject()) {
                        continue;
                    }
                    JsonObject row = parsed.getAsJsonObject();
                    if (!selected.isEmpty()
                            && !selected.equals(jsonString(row,
                            "activationId"))) {
                        continue;
                    }
                    if (!jsonBoolean(row, "replayable", true)) {
                        continue;
                    }
                    JsonElement materializations = row.get("materializations");
                    JsonElement legacy = row.get("symbolize");
                    JsonElement actions = materializations != null
                            && materializations.isJsonArray()
                            && materializations.getAsJsonArray().size() > 0
                            ? materializations : legacy;
                    if (actions == null || !actions.isJsonArray()) {
                        continue;
                    }
                    for (JsonElement element : actions.getAsJsonArray()) {
                        if (element.isJsonObject()) {
                            result.add(element.getAsJsonObject());
                        }
                    }
                }
            }
            if (!result.unsupported.isEmpty()) {
                throw new IOException("Unsupported concolic materialization: "
                        + result.unsupported);
            }
            return result;
        }

        private void add(JsonObject action) {
            addAccessorCallTarget(action);
            String mode = jsonString(action, "bindingMode");
            String cell = jsonString(action, "cell");
            if ("LOCAL_DEFINITION".equals(mode)) {
                String method = jsonString(action, "method");
                String local = jsonString(action, "local");
                Matcher matcher = LOCAL.matcher(cell);
                if (matcher.matches()) {
                    method = firstNonBlank(method, matcher.group(1));
                    local = firstNonBlank(local, matcher.group(2));
                }
                if (!method.isEmpty() && !local.isEmpty()) {
                    Map<String, Set<Integer>> locals =
                            localsByMethod.computeIfAbsent(method,
                                    ignored -> new LinkedHashMap<>());
                    Set<Integer> sites = locals.computeIfAbsent(local,
                            ignored -> new LinkedHashSet<>());
                    JsonElement definitions = action.get("definitionSites");
                    if (definitions != null && definitions.isJsonArray()) {
                        for (JsonElement element
                                : definitions.getAsJsonArray()) {
                            if (element.isJsonObject()) {
                                int site = intJson(element.getAsJsonObject(),
                                        "unitIndex", -1);
                                if (site >= 0) {
                                    sites.add(site);
                                }
                            }
                        }
                    }
                }
                if (declaresArrayValue(action)
                        && !exactArrayFieldPath(action).isEmpty()) {
                    addExactArrayLeafTarget(action);
                }
                return;
            }
            String location = jsonString(action, "location");
            if (declaresArrayValue(action)) {
                List<String> fieldPath = exactArrayFieldPath(action);
                boolean fieldBacked = !fieldPath.isEmpty()
                        || "FIELD_ACCESS".equals(mode)
                        || "FIELD".equals(location)
                        || "HEAP_OBJECT_FIELD".equals(location)
                        || "RECEIVER_FIELD".equals(location)
                        || "ARGUMENT_FIELD".equals(location)
                        || "ARGUMENT_FIELD_PATH".equals(location);
                if (fieldBacked) {
                    addExactArrayLeafTarget(action);
                }
                // A field-backed ARRAY_VALUE action must be hooked at the
                // actual leaf getfield, never at an earlier object-valued
                // component of a nested path.  Direct array arguments and
                // call returns have no getfield and remain handled by their
                // existing boundary hooks.
                return;
            }
            if (!"FIELD_ACCESS".equals(mode)
                    && !"HEAP_OBJECT_FIELD".equals(location)) {
                return;
            }
            String[] target = resolveConcolicFieldTarget(action);
            if (!target[1].isEmpty()) {
                fields.add(new FieldTarget(target[0], target[1]));
            }
        }

        private void addAccessorCallTarget(JsonObject action) {
            String caller = jsonString(action, "accessorCallerMethod");
            String site = jsonString(action, "accessorCallSiteId");
            int unitIndex = intJson(action, "accessorCallUnitIndex", -1);
            String callee = jsonString(action, "accessorDeclaredCallee");
            String authority = jsonString(action,
                    "accessorCallSiteAuthority");
            boolean constrained = !caller.isEmpty() || !site.isEmpty()
                    || unitIndex >= 0 || !callee.isEmpty()
                    || !authority.isEmpty();
            if (!constrained) return;
            if (caller.isEmpty() || unitIndex < 0 || callee.isEmpty()
                    || !site.equals(caller + "#u" + unitIndex)
                    || !ACCESSOR_CALLSITE_AUTHORITY.equals(authority)) {
                unsupported.add("ACCESSOR_CALL_CONTEXT_REQUIRES_EXACT_"
                        + "CALLSITE_METADATA:" + jsonString(action,
                        "symbol"));
                return;
            }
            AccessorCallTarget target = new AccessorCallTarget(caller,
                    unitIndex, site, callee);
            AccessorCallTarget previous = accessorCallsBySite.get(
                    target.siteIdentity());
            if (previous != null
                    && !previous.declaredCallee.equals(callee)) {
                unsupported.add("ACCESSOR_CALL_CONTEXT_AMBIGUOUS_DECLARED_"
                        + "CALLEE:" + site);
                return;
            }
            accessorCallsBySite.put(target.siteIdentity(), target);
        }

        private void addExactArrayLeafTarget(JsonObject action) {
            FieldTarget leaf = exactArrayLeafTarget(action);
            if (leaf == null) {
                unsupported.add("ARRAY_VALUE_FIELD_REQUIRES_EXACT_LEAF_"
                        + "DECLARATION_AND_CONSUMED_SITE:"
                        + jsonString(action, "symbol"));
            } else {
                fields.add(leaf);
            }
        }

        private static boolean declaresArrayValue(JsonObject action) {
            if (looksLikeArrayType(firstNonBlank(
                    jsonString(action, "javaType"),
                    jsonString(action, "inputJavaType")))) {
                return true;
            }
            for (String field : Arrays.asList(
                    jsonString(action, "leafFieldSignature"),
                    jsonString(action, "field"),
                    jsonString(action, "cell"))) {
                Matcher matcher = FIELD.matcher(field);
                if (matcher.matches() && looksLikeArrayType(matcher.group(2))) {
                    return true;
                }
            }
            JsonElement declarations = action.get(
                    "fieldPathLeafDeclarations");
            if (declarations != null && declarations.isJsonArray()) {
                for (JsonElement element : declarations.getAsJsonArray()) {
                    if (!element.isJsonObject()) continue;
                    Matcher matcher = FIELD.matcher(jsonString(
                            element.getAsJsonObject(), "fieldSignature"));
                    if (matcher.matches()
                            && looksLikeArrayType(matcher.group(2))) {
                        return true;
                    }
                }
            }
            return false;
        }

        private static FieldTarget exactArrayLeafTarget(JsonObject action) {
            String consumedMethod = jsonString(action,
                    "consumedFieldMethod");
            int consumedUnit = intJson(action, "consumedFieldUnitIndex", -1);
            String consumedSite = jsonString(action, "consumedFieldSiteId");
            String consumedAuthority = jsonString(action,
                    "consumedFieldSiteAuthority");
            if (!jsonBoolean(action, "consumedFieldBindingComplete", false)
                    || intJson(action, "consumedFieldOccurrence", -1) != 1
                    || !CONSUMED_OCCURRENCE_AUTHORITY.equals(jsonString(
                    action, "consumedFieldOccurrenceAuthority"))
                    || consumedMethod.isEmpty() || consumedUnit < 0
                    || !consumedSite.equals(consumedMethod + "#u"
                    + consumedUnit)
                    || !CONSUMED_SITE_AUTHORITY.equals(consumedAuthority)) {
                return null;
            }
            List<String> exactPath = exactArrayFieldPath(action);
            String rootAuthority = jsonString(action,
                    "consumedFieldRootAuthority");
            String location = jsonString(action, "location");
            String bindingMode = jsonString(action, "bindingMode");
            boolean argumentRoot = "ARGUMENT_FIELD".equals(location)
                    || "ARGUMENT_FIELD_PATH".equals(location);
            boolean receiverRoot = "RECEIVER_FIELD".equals(location);
            boolean localRoot = "LOCAL_DEFINITION".equals(bindingMode);
            boolean fieldAccessRoot = !argumentRoot && !receiverRoot
                    && !localRoot && ("FIELD_ACCESS".equals(bindingMode)
                    || "FIELD".equals(location)
                    || "HEAP_OBJECT_FIELD".equals(location));
            // A generic HEAP_OBJECT_FIELD can still be proven to be rooted at
            // the region receiver by runtime object identity.  The Runtime
            // registers receiver-authority actions at enterRegion regardless
            // of their observational location.  A direct field root has no
            // such entry identity and is intentionally limited to one leaf.
            boolean rootAuthorityMatches = argumentRoot
                    ? ARGUMENT_ROOT_AUTHORITY.equals(rootAuthority)
                    : receiverRoot
                    ? RECEIVER_ROOT_AUTHORITY.equals(rootAuthority)
                    : localRoot
                    ? LOCAL_ROOT_AUTHORITY.equals(rootAuthority)
                    : fieldAccessRoot && (RECEIVER_ROOT_AUTHORITY.equals(
                    rootAuthority) || exactPath.size() == 1
                    && DIRECT_ROOT_AUTHORITY.equals(rootAuthority));
            boolean rootBindingComplete = !argumentRoot
                    || intJson(action, "index", -1) >= 0;
            if (localRoot) {
                rootBindingComplete = hasOneExactLocalDefinition(action);
            }
            if (exactPath.isEmpty() || !rootAuthorityMatches
                    || !rootBindingComplete) {
                return null;
            }
            String expectedLeaf = jsonString(action, "leafField");
            if (!exactPath.isEmpty()) {
                expectedLeaf = exactPath.get(exactPath.size() - 1);
            }

            Set<String> signatures = new LinkedHashSet<>();
            signatures.add(jsonString(action, "leafFieldSignature"));
            signatures.add(jsonString(action, "field"));
            signatures.add(jsonString(action, "cell"));
            signatures.add(jsonString(action, "accessFieldSignature"));
            JsonElement declarations = action.get("fieldPathLeafDeclarations");
            if (declarations != null && declarations.isJsonArray()) {
                for (JsonElement element : declarations.getAsJsonArray()) {
                    if (element.isJsonObject()) {
                        signatures.add(jsonString(element.getAsJsonObject(),
                                "fieldSignature"));
                    }
                }
            }

            FieldTarget selected = null;
            for (String signature : signatures) {
                Matcher matcher = FIELD.matcher(stringValue(
                        firstNonBlank(signature)));
                if (!matcher.matches() || isMethodMember(matcher.group(3))
                        || !looksLikeArrayType(matcher.group(2))
                        || !expectedLeaf.isEmpty()
                        && !expectedLeaf.equals(matcher.group(3))) {
                    continue;
                }
                FieldTarget candidate = new FieldTarget(matcher.group(1),
                        matcher.group(3), consumedMethod, consumedUnit, true);
                if (selected != null
                        && (!selected.owner.equals(candidate.owner)
                        || !selected.name.equals(candidate.name)
                        || !selected.method.equals(candidate.method)
                        || selected.unitIndex != candidate.unitIndex)) {
                    return null;
                }
                selected = candidate;
            }
            return selected;
        }

        private static boolean hasOneExactLocalDefinition(JsonObject action) {
            String method = jsonString(action, "method");
            String local = jsonString(action, "local");
            Matcher localCell = LOCAL.matcher(jsonString(action, "cell"));
            if (localCell.matches()) {
                method = firstNonBlank(method, localCell.group(1));
                local = firstNonBlank(local, localCell.group(2));
            }
            JsonElement definitions = action.get("definitionSites");
            return !method.isEmpty() && !local.isEmpty()
                    && definitions != null && definitions.isJsonArray()
                    && definitions.getAsJsonArray().size() == 1
                    && definitions.getAsJsonArray().get(0).isJsonObject()
                    && intJson(definitions.getAsJsonArray().get(0)
                    .getAsJsonObject(), "unitIndex", -1) >= 0;
        }

        private static List<String> exactArrayFieldPath(JsonObject action) {
            List<String> path = new ArrayList<>();
            JsonElement direct = action.get("fieldPath");
            if (direct != null && direct.isJsonArray()) {
                for (JsonElement segment : direct.getAsJsonArray()) {
                    if (!segment.isJsonPrimitive()
                            || segment.getAsString().trim().isEmpty()) {
                        return Collections.emptyList();
                    }
                    path.add(segment.getAsString().trim());
                }
                if (!path.isEmpty()) return path;
            }
            JsonElement paths = action.get("fieldPaths");
            if (paths == null || !paths.isJsonArray()
                    || paths.getAsJsonArray().size() != 1
                    || !paths.getAsJsonArray().get(0).isJsonArray()) {
                return Collections.emptyList();
            }
            for (JsonElement segment : paths.getAsJsonArray().get(0)
                    .getAsJsonArray()) {
                if (!segment.isJsonPrimitive()
                        || segment.getAsString().trim().isEmpty()) {
                    return Collections.emptyList();
                }
                path.add(segment.getAsString().trim());
            }
            return path;
        }

        private static boolean looksLikeArrayType(String javaType) {
            String normalized = firstNonBlank(javaType);
            return normalized != null && (normalized.startsWith("[")
                    || normalized.endsWith("[]"));
        }

        private static String projectedField(String value) {
            if (value == null || value.isEmpty()) {
                return "";
            }
            int projection = value.indexOf("#field:");
            if (projection >= 0) {
                int end = value.indexOf('#', projection + 7);
                return value.substring(projection + 7,
                        end < 0 ? value.length() : end).trim();
            }
            Matcher matcher = FIELD.matcher(value);
            return matcher.matches() ? matcher.group(3) : "";
        }

        private boolean isEmpty() {
            return localsByMethod.isEmpty() && fields.isEmpty()
                    && accessorCallsBySite.isEmpty();
        }

        private Set<String> localMethods() {
            return localsByMethod.keySet();
        }

        private Set<String> accessorCallerMethods() {
            Set<String> methods = new LinkedHashSet<>();
            for (AccessorCallTarget target : accessorCallsBySite.values()) {
                methods.add(target.callerMethod);
            }
            return methods;
        }

        private Collection<AccessorCallTarget> accessorCalls() {
            return accessorCallsBySite.values();
        }

        private boolean matches(String method, String local, int unitIndex) {
            Map<String, Set<Integer>> locals = localsByMethod.get(method);
            if (locals == null || !locals.containsKey(local)) {
                return false;
            }
            Set<Integer> sites = locals.get(local);
            return sites.isEmpty() || sites.contains(unitIndex);
        }

        private static int intJson(JsonObject object, String field,
                                   int fallback) {
            JsonElement value = object.get(field);
            try {
                return value == null || value.isJsonNull()
                        ? fallback : value.getAsInt();
            } catch (RuntimeException ignored) {
                return fallback;
            }
        }

        private boolean matches(String method, int unitIndex,
                                SootFieldRef field) {
            if (field == null) {
                return false;
            }
            SootClass declaringClass = field.declaringClass();
            String owner = declaringClass == null ? ""
                    : stringValue(declaringClass.getName());
            String fieldName = stringValue(field.name());
            for (FieldTarget target : fields) {
                if (target.name.equals(fieldName)
                        && (target.owner.isEmpty()
                        || target.owner.equals(owner))
                        && (!target.exactSite
                        || target.method.equals(method)
                        && target.unitIndex == unitIndex)) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * Theory-neutral replay actions consumed by the bytecode transformer.
     * At present the protocol supports reference-valued assignment results;
     * additional value kinds can be added without importing project classes
     * or solver-specific logic into this layer.
     */
    private static final class ConcolicReplaySelection {
        private final Map<String, ReplayTarget> targetsBySite =
                new LinkedHashMap<>();

        private static ConcolicReplaySelection from(
                Path activationPlan, String selectedActivation)
                throws IOException {
            if (activationPlan == null || !Files.isRegularFile(activationPlan)) {
                throw new IOException("Activation plan not found: "
                        + activationPlan);
            }
            ConcolicReplaySelection result = new ConcolicReplaySelection();
            String selected = stringValue(firstNonBlank(selectedActivation));
            try (BufferedReader reader = Files.newBufferedReader(activationPlan,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) {
                        continue;
                    }
                    JsonElement parsed = JsonParser.parseString(line);
                    if (!parsed.isJsonObject()) {
                        continue;
                    }
                    JsonObject row = parsed.getAsJsonObject();
                    if (!selected.isEmpty()
                            && !selected.equals(jsonString(row,
                            "activationId"))) {
                        continue;
                    }
                    if (!jsonBoolean(row, "replayable", true)) {
                        continue;
                    }
                    JsonElement actions = row.get("replayMaterializations");
                    if (actions == null || !actions.isJsonArray()) {
                        continue;
                    }
                    for (JsonElement element : actions.getAsJsonArray()) {
                        if (!element.isJsonObject()) {
                            continue;
                        }
                        JsonObject action = element.getAsJsonObject();
                        if (!"REFERENCE_RESULT".equals(
                                jsonString(action, "kind"))) {
                            continue;
                        }
                        String method = jsonString(action, "method");
                        int unitIndex = ConcolicMaterializationSelection.intJson(
                                action, "unitIndex", -1);
                        if (!method.isEmpty() && unitIndex >= 0) {
                            ReplayTarget target = new ReplayTarget(method,
                                    unitIndex);
                            result.targetsBySite.put(
                                    method + "#u" + unitIndex, target);
                        }
                    }
                }
            }
            return result;
        }

        private Set<String> methods() {
            Set<String> result = new LinkedHashSet<>();
            for (ReplayTarget target : targetsBySite.values()) {
                result.add(target.method);
            }
            return result;
        }

        private Collection<ReplayTarget> targets() {
            return targetsBySite.values();
        }
    }

    private static final class ReplayTarget {
        private final String method;
        private final int unitIndex;

        private ReplayTarget(String method, int unitIndex) {
            this.method = method;
            this.unitIndex = unitIndex;
        }
    }

    /** Exact activation-selected outbound argument sites. */
    private static final class ConcolicOutputCaptureSelection {
        private final Map<String, OutputCaptureTarget> targetsByIdentity =
                new LinkedHashMap<>();

        private static ConcolicOutputCaptureSelection from(
                Path activationPlan, String selectedActivation)
                throws IOException {
            if (activationPlan == null || !Files.isRegularFile(
                    activationPlan)) {
                throw new IOException("Activation plan not found: "
                        + activationPlan);
            }
            ConcolicOutputCaptureSelection result =
                    new ConcolicOutputCaptureSelection();
            String selected = stringValue(firstNonBlank(selectedActivation));
            try (BufferedReader reader = Files.newBufferedReader(
                    activationPlan, StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) continue;
                    JsonElement parsed = JsonParser.parseString(line);
                    if (!parsed.isJsonObject()) continue;
                    JsonObject row = parsed.getAsJsonObject();
                    if (!selected.isEmpty() && !selected.equals(jsonString(
                            row, "activationId"))) continue;
                    if (!jsonBoolean(row, "replayable", true)) continue;
                    JsonElement captures = row.get(
                            "requestedOutputCapture");
                    if (captures == null || !captures.isJsonArray()) continue;
                    for (JsonElement element : captures.getAsJsonArray()) {
                        if (!element.isJsonObject()) continue;
                        OutputCaptureTarget target = new OutputCaptureTarget(
                                element.getAsJsonObject());
                        if (!target.valid()) continue;
                        result.targetsByIdentity.put(target.identity(), target);
                    }
                }
            }
            return result;
        }

        private Set<String> methods() {
            Set<String> result = new LinkedHashSet<>();
            for (OutputCaptureTarget target : targetsByIdentity.values()) {
                result.add(target.instrumentedMethod());
            }
            return result;
        }

        private Collection<OutputCaptureTarget> targets() {
            return targetsByIdentity.values();
        }
    }

    private static final class OutputCaptureTarget {
        private static final String CALL_ARGUMENT = "CALL_ARGUMENT";
        private static final String FIELD_ASSIGNMENT_RHS =
                "FIELD_ASSIGNMENT_RHS";

        private final String captureKind;
        private final String captureBindingId;
        private final String outputPort;
        private final String outputCell;
        private final String method;
        private final String callerMethod;
        private final int unitIndex;
        private final String siteId;
        private final String calleeMethod;
        private final int argumentIndex;
        private final String fieldSignature;
        private final int occurrence;

        private OutputCaptureTarget(JsonObject json) {
            this.captureKind = firstNonBlank(
                    jsonString(json, "captureKind"), CALL_ARGUMENT);
            this.captureBindingId = jsonString(json, "captureBindingId");
            this.outputPort = jsonString(json, "outputPort");
            this.outputCell = jsonString(json, "outputCell");
            this.callerMethod = jsonString(json, "callerMethod");
            this.method = stringValue(firstNonBlank(
                    jsonString(json, "method"), this.callerMethod));
            this.unitIndex = ConcolicMaterializationSelection.intJson(json,
                    "unitIndex", -1);
            this.siteId = jsonString(json, "siteId");
            this.calleeMethod = jsonString(json, "calleeMethod");
            this.argumentIndex = ConcolicMaterializationSelection.intJson(
                    json, "argumentIndex", -1);
            this.fieldSignature = stringValue(firstNonBlank(
                    jsonString(json, "fieldSignature"),
                    jsonString(json, "field")));
            this.occurrence = ConcolicMaterializationSelection.intJson(json,
                    "occurrence", 0);
        }

        private boolean valid() {
            if (captureBindingId.isEmpty() || outputPort.isEmpty()
                    || outputCell.isEmpty() || unitIndex < 0
                    || siteId.isEmpty() || occurrence <= 0) {
                return false;
            }
            if (FIELD_ASSIGNMENT_RHS.equals(captureKind)) {
                return !method.isEmpty() && !fieldSignature.isEmpty();
            }
            return CALL_ARGUMENT.equals(captureKind)
                    && !callerMethod.isEmpty() && !calleeMethod.isEmpty()
                    && argumentIndex >= 0;
        }

        private String identity() {
            return captureKind + "\n" + instrumentedMethod() + "\n"
                    + unitIndex + "\n" + siteId + "\n" + calleeMethod
                    + "\n" + argumentIndex + "\n" + fieldSignature + "\n"
                    + outputPort + "\n" + outputCell + "\n"
                    + captureBindingId + "\n" + occurrence;
        }

        private boolean isFieldAssignmentRhs() {
            return FIELD_ASSIGNMENT_RHS.equals(captureKind);
        }

        private String instrumentedMethod() {
            return isFieldAssignmentRhs() ? method : callerMethod;
        }
    }

    private static final class AccessorCallTarget {
        private final String callerMethod;
        private final int callUnitIndex;
        private final String callSiteId;
        private final String declaredCallee;

        private AccessorCallTarget(String callerMethod, int callUnitIndex,
                                   String callSiteId,
                                   String declaredCallee) {
            this.callerMethod = callerMethod;
            this.callUnitIndex = callUnitIndex;
            this.callSiteId = callSiteId;
            this.declaredCallee = declaredCallee;
        }

        private String siteIdentity() {
            return callerMethod + "#u" + callUnitIndex;
        }
    }

    private static final class FieldTarget {
        private final String owner;
        private final String name;
        private final String method;
        private final int unitIndex;
        private final boolean exactSite;

        private FieldTarget(String owner, String name) {
            this(owner, name, "", -1, false);
        }

        private FieldTarget(String owner, String name, String method,
                            int unitIndex, boolean exactSite) {
            String normalizedOwner = firstNonBlank(owner);
            String normalizedName = firstNonBlank(name);
            this.owner = normalizedOwner == null ? "" : normalizedOwner;
            this.name = normalizedName == null ? "" : normalizedName;
            String normalizedMethod = firstNonBlank(method);
            this.method = normalizedMethod == null ? "" : normalizedMethod;
            this.unitIndex = unitIndex;
            this.exactSite = exactSite;
        }
    }

    /** Wrapper metadata needed to round-trip primitive Jimple locals. */
    private static final class PrimitiveWrapper {
        private final String className;
        private final String unboxMethod;

        private PrimitiveWrapper(String className, String unboxMethod) {
            this.className = className;
            this.unboxMethod = unboxMethod;
        }

        private static PrimitiveWrapper forType(Type type) {
            if (type instanceof BooleanType) {
                return new PrimitiveWrapper("java.lang.Boolean", "booleanValue");
            }
            if (type instanceof ByteType) {
                return new PrimitiveWrapper("java.lang.Byte", "byteValue");
            }
            if (type instanceof ShortType) {
                return new PrimitiveWrapper("java.lang.Short", "shortValue");
            }
            if (type instanceof CharType) {
                return new PrimitiveWrapper("java.lang.Character", "charValue");
            }
            if (type instanceof IntType) {
                return new PrimitiveWrapper("java.lang.Integer", "intValue");
            }
            if (type instanceof LongType) {
                return new PrimitiveWrapper("java.lang.Long", "longValue");
            }
            if (type instanceof FloatType) {
                return new PrimitiveWrapper("java.lang.Float", "floatValue");
            }
            if (type instanceof DoubleType) {
                return new PrimitiveWrapper("java.lang.Double", "doubleValue");
            }
            return null;
        }
    }

    private static final class OriginalUnitIndexTag implements Tag {
        private static final String NAME = "CausynthOriginalUnitIndex";
        private final int index;

        private OriginalUnitIndexTag(int index) {
            this.index = index;
        }

        @Override
        public String getName() {
            return NAME;
        }

        @Override
        public byte[] getValue() {
            return new byte[]{
                    (byte) (index >>> 24),
                    (byte) (index >>> 16),
                    (byte) (index >>> 8),
                    (byte) index};
        }
    }

    private static final class TraceSiteSelection {
        private final Set<String> relevantMethods = new LinkedHashSet<>();
        private final Map<String, Set<Integer>> callUnits = new LinkedHashMap<>();
        private final Map<String, Set<Integer>> branchUnits = new LinkedHashMap<>();

        private void add(Map<String, Set<Integer>> sites, String method,
                         int unitIndex) {
            sites.computeIfAbsent(method, ignored -> new LinkedHashSet<>())
                    .add(unitIndex);
        }

        private Set<Integer> units(Map<String, Set<Integer>> sites,
                                   String method) {
            Set<Integer> values = sites.get(method);
            return values == null ? Collections.emptySet() : values;
        }
    }

    private static final class RichInstrumentationStats {
        private int callSites;
        private int branches;
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
        private final String seedException;
        private final String analysisScope;
        private TargetContext(Path repoRoot, Path moduleDir, Path outputDir,
                              Path specPath, List<String> seedVariables,
                              String seedFunction, String seedException,
                              String analysisScope) {
            this.repoRoot = repoRoot;
            this.moduleDir = moduleDir;
            this.outputDir = outputDir;
            this.specPath = specPath;
            this.seedVariables = seedVariables;
            this.seedFunction = seedFunction;
            this.seedException = seedException;
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
                    spec.seedVariables, spec.seedFunction, spec.seedException, scope);
        }

        boolean hasSeed() {
            return seedException != null && !seedException.trim().isEmpty()
                    || !seedVariables.isEmpty();
        }

        boolean exceptionSeeded() {
            return seedException != null && !seedException.trim().isEmpty();
        }

        String seedMode() {
            return exceptionSeeded() ? "EXCEPTION_AUTO" : "VARIABLE_COMPATIBILITY";
        }

        String seedDescription() {
            return exceptionSeeded() ? seedException : String.valueOf(seedVariables);
        }

        String seedPredicate() {
            if (exceptionSeeded()) {
                return "throws " + seedException;
            }
            if (seedVariables.size() >= 2) {
                return seedVariables.get(0) + ".get(" + seedVariables.get(1) + ") == null";
            }
            return seedVariables.isEmpty() ? "" : seedVariables.get(0);
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
        private final String seedException;

        private TargetSpec(List<String> seedVariables, String seedFunction,
                           String seedException) {
            this.seedVariables = seedVariables;
            this.seedFunction = seedFunction;
            this.seedException = seedException;
        }

        static TargetSpec load(Path path) throws IOException {
            if (!Files.isRegularFile(path)) {
                return new TargetSpec(Collections.emptyList(), null, null);
            }
            List<String> variables = new ArrayList<>();
            String seedFunction = null;
            String seedException = null;
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
                    if ("seed_exception".equals(key)
                            || "target_exception".equals(key)
                            || "exception".equals(key)) {
                        seedException = value;
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
            return new TargetSpec(variables, seedFunction, seedException);
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
        private final List<Map<String, Object>> symbolicPlan = new ArrayList<>();
        private final List<Map<String, Object>> symbolicRegions = new ArrayList<>();
        private final List<Map<String, Object>> symbolicRegionEdges = new ArrayList<>();
        private final List<Map<String, Object>> symbolicModels = new ArrayList<>();
        private final Map<String, Object> symbolicCoverage = object();
        private final Map<String, Object> automaticDerivationBoundary = object();
        private final Map<String, Object> slices = object();
        private final Map<String, Object> targetResolved = object();
    }

    private static final class SeedBackwardStaticAnalyzer {
        private static final int MAX_ROUNDS = 96;
        private static final int MAX_METHODS = 1000;
        private static final int MAX_EDGES = 50000;
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
        private final Map<String, Set<String>> relevantFieldEffectsByMethod =
                new LinkedHashMap<>();
        private final List<StaticPortMapping> staticPortMappings = new ArrayList<>();
        private final Map<String, Set<String>> relevantByMethod = new LinkedHashMap<>();
        private final Set<String> selectedMethods = new LinkedHashSet<>();
        private final Set<String> emittedEdges = new LinkedHashSet<>();
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

        private SeedBackwardStaticAnalyzer(TargetContext target) {
            this.target = target;
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

        AnalysisResult analyze() throws IOException {
            AnalysisResult result = new AnalysisResult();
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
            return result;
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

        private void finishSeedDiscovery(AnalysisResult result) {
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
                        }
                        pathGuards.add(object(
                                "siteId", stableSiteId(method,
                                        guard.fact.unitIndex, "exception_guard"),
                                "line", guard.fact.line,
                                "unitIndex", guard.fact.unitIndex,
                                "jimpleCondition", guard.condition,
                                "requiredOutcome", guard.requiredOutcome,
                                "reachingSuccessorIndices",
                                guard.reachingSuccessorIndices));
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
                List<Unit> successors = graph.getSuccsOf(candidate.unit);
                if (successors.size() < 2) {
                    continue;
                }
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
                                requiredOutcome, reachingIndices));
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
            for (int round = 0; round < MAX_ROUNDS && edges.size() < MAX_EDGES; round++) {
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
                    // MAX_METHODS limits admission of new static candidates;
                    // it must not prevent already admitted methods from
                    // reaching their fixed point.  The previous early break
                    // left the tail of selectedMethods unprocessed whenever
                    // the cap was reached (trace-visible methods could then
                    // have zero data-flow edges).
                    if (edges.size() >= MAX_EDGES) {
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
                        changed |= addEdge("path_guard_dependency", guardNode, def,
                                method, guard.fact,
                                "dominating branch requires Jimple outcome "
                                        + guard.requiredOutcome
                                        + " to reach relevant definition at u"
                                        + targetFact.unitIndex);
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
                    mutatedCell, method);
            Map<String, Object> edge = emittedEdgeRows.get(key);
            if (edge == null) {
                return changed;
            }

            String guardSiteId = stableSiteId(method,
                    guard.fact.unitIndex, "heap_mutation_path_guard");
            String mutationSiteId = stableSiteId(method,
                    mutation.unitIndex, "field_mutation");
            edge.put("guardSiteId", guardSiteId);
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> guardedMutations =
                    edge.get("guardedMutations") instanceof List
                            ? (List<Map<String, Object>>) edge.get(
                            "guardedMutations") : new ArrayList<>();
            if (!edge.containsKey("guardedMutations")) {
                edge.put("guardedMutations", guardedMutations);
            }
            boolean present = false;
            for (Map<String, Object> item : guardedMutations) {
                if (mutationSiteId.equals(stringValue(
                        item.get("guardedMutationSiteId")))
                        && java.util.Objects.equals(guard.requiredOutcome,
                        item.get("requiredOutcome"))) {
                    present = true;
                    break;
                }
            }
            if (!present) {
                guardedMutations.add(object(
                        "guardSiteId", guardSiteId,
                        "guardedMutationSiteId", mutationSiteId,
                        "method", method,
                        "unitIndex", mutation.unitIndex,
                        "requiredOutcome", guard.requiredOutcome));
                changed = true;
            }
            edge.put("guardedMutationCount", guardedMutations.size());
            edge.put("guardedMutationsAuthority",
                    "STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE");
            if (guardedMutations.size() == 1) {
                edge.put("guardedMutationSiteId", mutationSiteId);
                edge.put("requiredOutcome", guard.requiredOutcome);
            } else {
                // The array is authoritative when one guard/state dependency
                // represents several mutation sites (possibly on opposite
                // successors). A singular alias would silently discard that
                // distinction, so remove it once cardinality exceeds one.
                edge.remove("guardedMutationSiteId");
                edge.remove("requiredOutcome");
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
                    callsite.method));
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
                    guardNode, effectField, callsite.method));
            if (edge == null) {
                return changed;
            }
            String guardSiteId = stableSiteId(callsite.method,
                    guard.fact.unitIndex, kind);
            String effectSiteId = stableSiteId(callsite.method,
                    callsite.fact.unitIndex,
                    "method_receiver_field_effect");
            edge.put("guardSiteId", guardSiteId);
            edge.put("calleeMethod", calleeMethod);
            edge.put("effectField", effectField);
            edge.put("effectSiteId", effectSiteId);
            edge.put("effectAuthority",
                    "GLOBAL_WRITER_INDEX_AND_EXACT_CALLSITE_CONTROL_DEPENDENCE_V1");
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> effects =
                    edge.get("guardedEffects") instanceof List
                            ? (List<Map<String, Object>>) edge.get(
                            "guardedEffects") : new ArrayList<>();
            if (!edge.containsKey("guardedEffects")) {
                edge.put("guardedEffects", effects);
            }
            boolean present = effects.stream().anyMatch(item ->
                    effectSiteId.equals(stringValue(item.get("effectSiteId")))
                            && java.util.Objects.equals(
                            guard.requiredOutcome,
                            item.get("requiredOutcome")));
            if (!present) {
                effects.add(object(
                        "guardSiteId", guardSiteId,
                        "effectSiteId", effectSiteId,
                        "calleeMethod", calleeMethod,
                        "effectField", effectField,
                        "unitIndex", callsite.fact.unitIndex,
                        "requiredOutcome", guard.requiredOutcome));
                changed = true;
            }
            edge.put("guardedEffectCount", effects.size());
            edge.put("guardedEffectsAuthority",
                    "STATIC_CONTROL_DEPENDENCE_PER_RECEIVER_EFFECT_SITE_V1");
            if (effects.size() == 1) {
                edge.put("requiredOutcome", guard.requiredOutcome);
            } else {
                edge.remove("requiredOutcome");
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
            if (expandableCallee && (selectedMethods.size() < MAX_METHODS
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
                        receiverNode, def, callerMethod));
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
                            callerMethod, declaredField, declaredAccessor);
                }
                if (addEdge("accessor_field_return", receiverField, def,
                        callerMethod, fact,
                        "accessor return reads receiver-local field projection")) {
                    changed = true;
                }
                if (declaredField != null) {
                    annotateAccessorDeclaredFieldEdge(receiverField, def,
                            callerMethod, declaredField, declaredAccessor);
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
                String from, String to, String method, SootField field,
                SootMethod accessor) {
            Map<String, Object> edge = emittedEdgeRows.get(edgeKey(
                    "accessor_field_return", from, to, method));
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
                targetMethods = demandedDispatchTargets(targetMethods, defs,
                        actuals, callerRelevant);
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
                } else if (selectedMethods.size() < MAX_METHODS) {
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
         * If the backward slice reached an interface call from an already
         * demanded concrete implementation, retain that implementation instead
         * of reopening every class-wide dispatch candidate.  Calls first
         * reached at the interface remain conservatively over-approximated.
         */
        private List<String> demandedDispatchTargets(List<String> targets,
                                                     List<String> callerDefs,
                                                     List<String> callerActuals,
                                                     Set<String> callerRelevant) {
            if (!intersects(callerRelevant, callerDefs)
                    && !intersects(callerRelevant, callerActuals)) {
                return targets;
            }
            List<String> demanded = new ArrayList<>();
            for (String target : targets) {
                Set<String> relevant = relevantByMethod.get(target);
                if (selectedMethods.contains(target) && relevant != null
                        && !relevant.isEmpty()) {
                    demanded.add(target);
                }
            }
            return demanded.isEmpty() ? targets : demanded;
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
                    if (selectedMethods.size() >= MAX_METHODS
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
                    changed |= addEdge("synchronous_callback_path_guard",
                            guardNode, dataflow.targetCell,
                            dataflow.pathSite.method, guard.fact,
                            "synchronous callback invocation requires Jimple outcome "
                                    + guard.requiredOutcome + " at callback site u"
                                    + dataflow.pathSite.unitIndex);
                    changed |= pathRelevant.add(guardNode);
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
            List<String> uses = new ArrayList<>();
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
                uses.add(use);
            }
            return uses;
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
            if (edges.size() >= MAX_EDGES || from == null || to == null) {
                return false;
            }
            String fromText = String.valueOf(from);
            String toText = String.valueOf(to);
            if (ignoreNode(fromText) || ignoreNode(toText) || fromText.equals(toText)) {
                return false;
            }
            String key = edgeKey(kind, fromText, toText, method);
            boolean changed = false;
            Map<String, Object> edge = emittedEdgeRows.get(key);
            if (emittedEdges.add(key)) {
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
                String edgeTransferKind = transferKind(kind,
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
                            "SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
                    edge.put("directCopyKind",
                            fact.unit instanceof ReturnStmt
                                    ? "RETURN_LOCAL" : "LOCAL_ASSIGN_LOCAL");
                } else if (projectedDirectCopy) {
                    edge.put("valueFlowAuthority",
                            "PROJECTED_FROM_SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
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
                    || !"SOOT_EXACT_LOCAL_DIRECT_COPY_V1".equals(
                    stringValue(baseEdge.get("valueFlowAuthority")))) {
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
            return kind + "\n" + String.valueOf(from) + "\n"
                    + String.valueOf(to) + "\n" + method;
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

    private static final class StaticPortMapping {
        private final String kind;
        private final String sourceMethod;
        private final String sourceCell;
        private final String targetMethod;
        private final String targetCell;
        private final String evidence;
        private final String activationMethod;
        private final String edgeMethod;
        private final Fact pathSite;
        private final String pathCell;

        private StaticPortMapping(String kind, String sourceMethod, String sourceCell,
                                  String targetMethod, String targetCell,
                                  String evidence, String activationMethod,
                                  String edgeMethod, Fact pathSite,
                                  String pathCell) {
            this.kind = kind;
            this.sourceMethod = sourceMethod;
            this.sourceCell = sourceCell;
            this.targetMethod = targetMethod;
            this.targetCell = targetCell;
            this.evidence = evidence;
            this.activationMethod = activationMethod;
            this.edgeMethod = edgeMethod;
            this.pathSite = pathSite;
            this.pathCell = pathCell;
        }
    }

    private static final class CallbackRegistration {
        private final String handlerCell;
        private final String implementationCell;
        private final String implementationMethod;

        private CallbackRegistration(String handlerCell,
                                     String implementationCell,
                                     String implementationMethod) {
            this.handlerCell = handlerCell;
            this.implementationCell = implementationCell;
            this.implementationMethod = implementationMethod;
        }
    }

    private static final class MappedEndpoint {
        private final String method;
        private final String cell;

        private MappedEndpoint(String method, String cell) {
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

    private static final class ExceptionConstruction {
        private final Fact fact;
        private final List<String> actuals;

        private ExceptionConstruction(Fact fact, List<String> actuals) {
            this.fact = fact;
            this.actuals = actuals;
        }
    }

    /**
     * Exact runtime interface-dispatch observations used by an optional
     * second static/refinement pass.  The file is never discovered by walking
     * old output directories: callers must pass one explicit artifact via
     * causynth.runtime.call.edges (or CAUSYNTH_RUNTIME_CALL_EDGES).
     */
    private static final class RuntimeDispatchEvidence {
        private final String source;
        private final Map<String, RuntimeDispatchObservation> observations;
        private final int rowCount;
        private final int rejectedRowCount;

        private RuntimeDispatchEvidence(
                String source,
                Map<String, RuntimeDispatchObservation> observations,
                int rowCount, int rejectedRowCount) {
            this.source = source;
            this.observations = observations;
            this.rowCount = rowCount;
            this.rejectedRowCount = rejectedRowCount;
        }

        private static RuntimeDispatchEvidence fromConfiguration()
                throws IOException {
            String configured = stringValue(firstNonBlank(
                    System.getProperty("causynth.runtime.call.edges"),
                    System.getenv("CAUSYNTH_RUNTIME_CALL_EDGES")));
            if (configured.isEmpty()) {
                return new RuntimeDispatchEvidence("",
                        new LinkedHashMap<>(), 0, 0);
            }
            Path path = Paths.get(configured).toAbsolutePath().normalize();
            if (!Files.isRegularFile(path)) {
                throw new IOException("Runtime call-edge evidence not found: "
                        + path);
            }
            Map<String, RuntimeDispatchObservation> observations =
                    new LinkedHashMap<>();
            int rows = 0;
            int rejected = 0;
            try (BufferedReader reader = Files.newBufferedReader(path,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    String trimmed = line.trim();
                    if (trimmed.isEmpty()) {
                        continue;
                    }
                    rows++;
                    JsonObject row;
                    try {
                        JsonElement parsed = JsonParser.parseString(trimmed);
                        if (!parsed.isJsonObject()) {
                            rejected++;
                            continue;
                        }
                        row = parsed.getAsJsonObject();
                    } catch (RuntimeException malformed) {
                        rejected++;
                        continue;
                    }
                    String event = jsonString(row, "event");
                    String caller = jsonString(row, "caller");
                    String siteId = jsonString(row, "siteId");
                    String declared = jsonString(row, "declaredCallee");
                    String actual = jsonString(row, "actualCallee");
                    String level = jsonString(row, "evidenceLevel");
                    if (!"RUNTIME_CALL_EDGE".equals(event)
                            || !"CALLSITE_CORRELATED".equals(level)
                            || caller.isEmpty() || siteId.isEmpty()
                            || declared.isEmpty() || actual.isEmpty()
                            || !siteId.startsWith(caller + "#u")) {
                        rejected++;
                        continue;
                    }
                    String key = key(caller, siteId, declared);
                    RuntimeDispatchObservation observation =
                            observations.computeIfAbsent(key,
                                    ignored -> new RuntimeDispatchObservation(
                                            caller, siteId, declared));
                    observation.actualCallees.add(actual);
                }
            }
            return new RuntimeDispatchEvidence(path.toString(),
                    observations, rows, rejected);
        }

        private RuntimeDispatchObservation lookup(String caller,
                                                   String siteId,
                                                   String declared) {
            return observations.get(key(caller, siteId, declared));
        }

        private static String key(String caller, String siteId,
                                  String declared) {
            return stringValue(caller) + "\n" + stringValue(siteId) + "\n"
                    + stringValue(declared);
        }

        private boolean configured() {
            return !source.isEmpty();
        }

        private String source() {
            return source;
        }

        private int rowCount() {
            return rowCount;
        }

        private int siteCount() {
            return observations.size();
        }

        private int rejectedRowCount() {
            return rejectedRowCount;
        }
    }

    private static final class RuntimeDispatchObservation {
        private final String caller;
        private final String siteId;
        private final String declaredCallee;
        private final Set<String> actualCallees = new LinkedHashSet<>();

        private RuntimeDispatchObservation(String caller, String siteId,
                                           String declaredCallee) {
            this.caller = caller;
            this.siteId = siteId;
            this.declaredCallee = declaredCallee;
        }
    }

    private static final class RuntimeDispatchSelection {
        private final String siteId;
        private final List<String> targets;
        private final Set<String> actualCallees;
        private final String source;
        private final String reason;
        private final boolean runtimeSelected;

        private RuntimeDispatchSelection(String siteId,
                                         Collection<String> targets,
                                         Collection<String> actualCallees,
                                         String source, String reason,
                                         boolean runtimeSelected) {
            this.siteId = stringValue(siteId);
            this.targets = new ArrayList<>(targets);
            this.actualCallees = new LinkedHashSet<>(actualCallees);
            this.source = stringValue(source);
            this.reason = stringValue(reason);
            this.runtimeSelected = runtimeSelected;
        }

        private static RuntimeDispatchSelection staticFallback(
                String siteId, Collection<String> targets) {
            return new RuntimeDispatchSelection(siteId, targets,
                    Collections.emptySet(), "", "", false);
        }

        private static RuntimeDispatchSelection runtimeUnique(
                String siteId, String target, String source) {
            return new RuntimeDispatchSelection(siteId,
                    Collections.singletonList(target),
                    Collections.singleton(target), source, "", true);
        }

        private static RuntimeDispatchSelection blocked(
                String siteId, Collection<String> actualCallees,
                String reason) {
            return new RuntimeDispatchSelection(siteId,
                    Collections.emptyList(), actualCallees, "", reason,
                    true);
        }

        private RuntimeDispatchSelection withReason(String updatedReason) {
            return new RuntimeDispatchSelection(siteId, targets,
                    actualCallees, source, updatedReason, runtimeSelected);
        }

        private boolean unique() {
            return runtimeSelected && reason.isEmpty()
                    && targets.size() == 1;
        }

        private boolean blocked() {
            return !reason.isEmpty();
        }
    }

    private static final class ExceptionGuard {
        private final Fact fact;
        private final String condition;
        private final Boolean requiredOutcome;
        private final List<Integer> reachingSuccessorIndices;

        private ExceptionGuard(Fact fact, String condition,
                               Boolean requiredOutcome,
                               List<Integer> reachingSuccessorIndices) {
            this.fact = fact;
            this.condition = condition;
            this.requiredOutcome = requiredOutcome;
            this.reachingSuccessorIndices = reachingSuccessorIndices;
        }
    }

    private static final class Fact {
        private final Unit unit;
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
            this.unit = unit;
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

    private static void buildSymbolicExecutionPlan(AnalysisResult result) {
        Map<String, SymbolicPlanBuilder> builders = new LinkedHashMap<>();
        for (Map<String, Object> edge : result.edges) {
            String method = stringValue(edge.get("method"));
            if (method.isEmpty()) {
                continue;
            }
            String kind = stringValue(edge.get("kind"));
            String unit = stringValue(edge.get("unit"));
            String invoke = stringValue(edge.get("invoke"));
            String from = stringValue(edge.get("fromCell"));
            String to = stringValue(edge.get("toCell"));
            String transfer = stringValue(edge.get("transferKind"));
            if (transfer.isEmpty()) {
                transfer = transferKind(kind, unit, invoke, from, to);
                edge.put("transferKind", transfer);
            }
            String siteId = stringValue(edge.get("siteId"));
            if (siteId.isEmpty()) {
                siteId = stableSiteId(method, intValue(edge.get("unitIndex"), -1), kind);
                edge.put("siteId", siteId);
            }
            SymbolicPlanBuilder builder = builders.get(method);
            if (builder == null) {
                builder = new SymbolicPlanBuilder(method);
                builders.put(method, builder);
            }
            builder.observe(edge, transfer, siteId);
        }

        List<SymbolicPlanBuilder> ordered = new ArrayList<>(builders.values());
        ordered.sort(Comparator.comparing(builder -> builder.method));
        int index = 0;
        for (SymbolicPlanBuilder builder : ordered) {
            result.symbolicPlan.add(builder.toRow("SP." + index++));
        }
        result.slices.put("symbolicPlanMethodCount", result.symbolicPlan.size());
        result.slices.put("symbolicPlanClassifications",
                summarizePlanClassifications(result.symbolicPlan));
    }

    /**
     * Groups method summaries into same-thread concolic regions. Protocol,
     * asynchronous, and thread-handoff edges deliberately remain between
     * regions so the later composer can bind their symbolic ports without
     * pretending that one JVM invocation crosses those execution contexts.
     */
    private static void buildSymbolicRegions(AnalysisResult result) {
        SymbolicRegionPlanner.Result planned = SymbolicRegionPlanner.plan(
                result.edges, result.symbolicPlan);
        enrichHeapMutationGuardMetadata(planned.regions, result.edges);
        addArgumentPathFieldContracts(planned.regions);
        result.symbolicRegions.addAll(planned.regions);
        result.symbolicRegionEdges.addAll(planned.regionEdges);
        result.symbolicModels.addAll(planned.modelSummaries);
        result.symbolicCoverage.putAll(planned.coverage);
        result.slices.put("symbolicRegions", planned.summary);
        result.slices.put("symbolicCoverage", planned.coverage);
    }

    /**
     * The region planner keeps compact causal-edge references in each output
     * slice. Reattach the structured control-dependence proof required to
     * distinguish a path which executes a may-write from a path which proves
     * the guarded mutation unreachable. This is a lossless id join; no
     * project-specific method or field names participate.
     */
    static void enrichHeapMutationGuardMetadata(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> analysisEdges) {
        Map<String, Map<String, Object>> byId = new LinkedHashMap<>();
        for (Map<String, Object> edge : analysisEdges) {
            if ("heap_mutation_path_guard".equals(
                    stringValue(edge.get("kind")))) {
                byId.put(stringValue(edge.get("id")), edge);
            }
        }
        for (Map<String, Object> region : regions) {
            Object slicesValue = region.get("outputSlices");
            if (!(slicesValue instanceof Collection)) {
                continue;
            }
            for (Object sliceValue : (Collection<?>) slicesValue) {
                if (!(sliceValue instanceof Map)) {
                    continue;
                }
                Map<?, ?> slice = (Map<?, ?>) sliceValue;
                Object referencesValue = slice.get("causalEdges");
                if (!(referencesValue instanceof Collection)) {
                    continue;
                }
                for (Object referenceValue
                        : (Collection<?>) referencesValue) {
                    if (!(referenceValue instanceof Map)) {
                        continue;
                    }
                    @SuppressWarnings("unchecked")
                    Map<String, Object> reference =
                            (Map<String, Object>) referenceValue;
                    Map<String, Object> source = byId.get(stringValue(
                            reference.get("edgeId")));
                    if (source == null) {
                        continue;
                    }
                    copyIfPresent(source, reference, "guardSiteId");
                    copyIfPresent(source, reference,
                            "guardedMutationSiteId");
                    copyIfPresent(source, reference, "requiredOutcome");
                    copyIfPresent(source, reference,
                            "guardedMutationCount");
                    copyIfPresent(source, reference,
                            "guardedMutationsAuthority");
                    copyIfPresent(source, reference, "guardedMutations");
                }
            }
        }
    }

    private static void copyIfPresent(Map<String, Object> source,
                                      Map<String, Object> target,
                                      String field) {
        if (source.containsKey(field)) {
            target.put(field, source.get(field));
        }
    }

    /**
     * Records root-argument fields that can influence a branch executed after
     * a candidate region entry.
     *
     * <p>The seed-directed slice is deliberately narrow and can omit an
     * earlier path gate.  For example, the HDFS missing-key seed retains
     * {@code getKeyId()} but not the preceding expiry check.  A concolic
     * region nevertheless starts before both checks, so every external field
     * feeding either branch is part of its input frontier.  This small
     * intraprocedural pass supplies that entry contract without widening the
     * whole symbolic region.</p>
     */
    private static void addArgumentPathFieldContracts(
            List<Map<String, Object>> regions) {
        for (Map<String, Object> region : regions) {
            Object methodsValue = region.get("methods");
            if (!(methodsValue instanceof Collection)) {
                continue;
            }
            List<Map<String, Object>> contracts = new ArrayList<>();
            for (Object methodValue : (Collection<?>) methodsValue) {
                String signature = stringValue(methodValue);
                if (signature.isEmpty()) {
                    continue;
                }
                try {
                    SootMethod method = Scene.v().getMethod(signature);
                    if (method != null && method.isConcrete()) {
                        contracts.addAll(argumentPathFieldContracts(method));
                    }
                } catch (RuntimeException ignored) {
                    // Runtime root selection may still use the dynamic getter
                    // observations when a candidate body is unavailable.
                }
            }
            if (!contracts.isEmpty()) {
                region.put("argumentPathFields", contracts);
            }
        }
    }

    private static List<Map<String, Object>> argumentPathFieldContracts(
            SootMethod method) {
        Body body;
        try {
            body = method.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return Collections.emptyList();
        }
        List<Unit> units = snapshotUnits(body);
        Map<Local, Set<Integer>> argumentAliases = new LinkedHashMap<>();
        Map<Local, Set<ArgumentFieldOrigin>> fieldOrigins = new LinkedHashMap<>();
        for (Unit unit : units) {
            if (!(unit instanceof IdentityStmt)) {
                continue;
            }
            IdentityStmt identity = (IdentityStmt) unit;
            if (identity.getLeftOp() instanceof Local
                    && identity.getRightOp() instanceof ParameterRef) {
                addValue(argumentAliases, (Local) identity.getLeftOp(),
                        ((ParameterRef) identity.getRightOp()).getIndex());
            }
        }

        // Iterate to a fixed point so aliases and value flow remain correct
        // for non-linear Jimple bodies as well as the common straight-line
        // getter -> helper -> branch shape.
        boolean changed = true;
        int rounds = 0;
        while (changed && rounds++ <= units.size() + 1) {
            changed = false;
            for (Unit unit : units) {
                if (!(unit instanceof AssignStmt)) {
                    continue;
                }
                AssignStmt assignment = (AssignStmt) unit;
                if (!(assignment.getLeftOp() instanceof Local)) {
                    continue;
                }
                Local left = (Local) assignment.getLeftOp();
                Value right = assignment.getRightOp();
                changed |= addValues(argumentAliases, left,
                        directArgumentAliases(right, argumentAliases));

                Set<ArgumentFieldOrigin> origins = new LinkedHashSet<>();
                for (ValueBox box : right.getUseBoxes()) {
                    if (box.getValue() instanceof Local) {
                        origins.addAll(values(fieldOrigins,
                                (Local) box.getValue()));
                    }
                }
                if (right instanceof InstanceFieldRef) {
                    InstanceFieldRef field = (InstanceFieldRef) right;
                    if (field.getBase() instanceof Local) {
                        for (Integer index : values(argumentAliases,
                                (Local) field.getBase())) {
                            origins.add(new ArgumentFieldOrigin(index,
                                    field.getFieldRef().name()));
                        }
                    }
                }
                if (right instanceof InstanceInvokeExpr) {
                    InstanceInvokeExpr invoke = (InstanceInvokeExpr) right;
                    if (invoke.getBase() instanceof Local) {
                        String field = getterFieldName(invoke);
                        if (!field.isEmpty()) {
                            for (Integer index : values(argumentAliases,
                                    (Local) invoke.getBase())) {
                                origins.add(new ArgumentFieldOrigin(index, field));
                            }
                        }
                    }
                }
                changed |= addValues(fieldOrigins, left, origins);
            }
        }

        Map<Integer, Set<String>> fieldsByArgument = new LinkedHashMap<>();
        Map<Integer, Set<String>> sitesByArgument = new LinkedHashMap<>();
        for (int unitIndex = 0; unitIndex < units.size(); unitIndex++) {
            Unit unit = units.get(unitIndex);
            if (!(unit instanceof IfStmt)) {
                continue;
            }
            Set<ArgumentFieldOrigin> origins = new LinkedHashSet<>();
            for (ValueBox box : ((IfStmt) unit).getCondition().getUseBoxes()) {
                if (box.getValue() instanceof Local) {
                    origins.addAll(values(fieldOrigins, (Local) box.getValue()));
                }
            }
            for (ArgumentFieldOrigin origin : origins) {
                addValue(fieldsByArgument, origin.argumentIndex, origin.field);
                addValue(sitesByArgument, origin.argumentIndex,
                        stableSiteId(method.getSignature(), unitIndex, "branch"));
            }
        }

        List<Map<String, Object>> result = new ArrayList<>();
        for (Integer argumentIndex : fieldsByArgument.keySet()) {
            result.add(object(
                    "method", method.getSignature(),
                    "argumentIndex", argumentIndex,
                    "fields", sortedLimited(fieldsByArgument.get(argumentIndex),
                            MAX_ROOT_ARGUMENT_PATH_FIELDS),
                    "branchSites", sortedLimited(sitesByArgument.get(argumentIndex),
                            MAX_ROOT_ARGUMENT_PATH_FIELDS),
                    "authority", "STATIC_ROOT_BRANCH_DATAFLOW"));
        }
        return result;
    }

    private static final int MAX_ROOT_ARGUMENT_PATH_FIELDS = 64;

    private static Set<Integer> directArgumentAliases(
            Value value, Map<Local, Set<Integer>> aliases) {
        if (value instanceof Local) {
            return values(aliases, (Local) value);
        }
        if (value instanceof CastExpr
                && ((CastExpr) value).getOp() instanceof Local) {
            return values(aliases, (Local) ((CastExpr) value).getOp());
        }
        return Collections.emptySet();
    }

    private static String getterFieldName(InstanceInvokeExpr invoke) {
        if (invoke.getArgCount() != 0) {
            return "";
        }
        String name = invoke.getMethodRef().name();
        String stem;
        if (name.startsWith("get") && name.length() > 3) {
            stem = name.substring(3);
        } else if (name.startsWith("is") && name.length() > 2) {
            stem = name.substring(2);
        } else {
            return "";
        }
        return Character.toLowerCase(stem.charAt(0)) + stem.substring(1);
    }

    private static <K, V> Set<V> values(Map<K, Set<V>> values, K key) {
        Set<V> result = values.get(key);
        return result == null ? Collections.emptySet() : result;
    }

    private static <K, V> boolean addValue(Map<K, Set<V>> values,
                                            K key, V value) {
        return values.computeIfAbsent(key, ignored -> new LinkedHashSet<>())
                .add(value);
    }

    private static <K, V> boolean addValues(Map<K, Set<V>> values,
                                             K key, Collection<V> additions) {
        return additions != null && !additions.isEmpty()
                && values.computeIfAbsent(key, ignored -> new LinkedHashSet<>())
                .addAll(additions);
    }

    private static final class ArgumentFieldOrigin {
        private final int argumentIndex;
        private final String field;

        private ArgumentFieldOrigin(int argumentIndex, String field) {
            this.argumentIndex = argumentIndex;
            this.field = field;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof ArgumentFieldOrigin)) {
                return false;
            }
            ArgumentFieldOrigin that = (ArgumentFieldOrigin) other;
            return argumentIndex == that.argumentIndex && field.equals(that.field);
        }

        @Override
        public int hashCode() {
            return 31 * argumentIndex + field.hashCode();
        }
    }

    private static void buildAutomaticDerivationBoundary(AnalysisResult result) {
        Map<String, Object> boundary = result.automaticDerivationBoundary;
        boundary.put("schemaVersion", 1);
        boundary.put("kind", "AUTOMATIC_DERIVATION_BOUNDARY");
        boundary.put("complete", true);
        boundary.put("domainSemanticAdapterUsed", false);
        boundary.put("staticPortMappingsAreSemanticAssertions", false);
        boundary.put("automaticEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT_ONLY");
        boundary.put("automaticStateAuthority",
                "RUNTIME_CONFIRMED_WRITE_READ_PAIR_ONLY");
        boundary.put("explicitContractsIncludedInSmt", false);
        boundary.put("scope", stringValue(result.targetResolved.get(
                "analysisScope")));
        result.slices.put("automaticDerivationBoundary", boundary);
    }

    private static String transferKind(String kind, String unit, String invoke,
                                       String from, String to) {
        String normalizedKind = lower(kind);
        String text = lower(firstNonBlank(unit, "") + "\n"
                + firstNonBlank(invoke, "") + "\n"
                + firstNonBlank(from, "") + "\n"
                + firstNonBlank(to, ""));
        if (normalizedKind.contains("seed")) {
            return "SEED";
        }
        if (normalizedKind.contains("guard")) {
            return "GUARD";
        }
        if (normalizedKind.contains("throw")) {
            return "EXCEPTION";
        }
        if (normalizedKind.contains("hdfs_sasl")
                || normalizedKind.contains("hdfs_heartbeat")
                || normalizedKind.contains("rpc")) {
            return "PROTOCOL_TRANSFER";
        }
        if (normalizedKind.contains("dispatch")) {
            return "DYNAMIC_DISPATCH";
        }
        if (normalizedKind.contains("field_write")
                || normalizedKind.contains("field_mutation")
                || normalizedKind.contains("field_effect")) {
            return "HEAP_WRITE";
        }
        if (normalizedKind.contains("field_read")) {
            return "HEAP_READ";
        }
        if (normalizedKind.startsWith("container_")) {
            return "MODEL_TRANSFORM";
        }
        if (normalizedKind.contains("accessor")
                && from != null
                && from.matches("<[^:]+:\\s+.+\\s+[^\\s()]+>")
                && parseMethodSig(from) == null) {
            // An accessor backed by a Soot-resolved declared field is a real
            // heap read. Receiver-local projections of the same access remain
            // PROJECTION edges below so object-sensitive runtime provenance is
            // preserved without losing the canonical field frontier.
            return "HEAP_READ";
        }
        if (looksLikeMapMutation(text)) {
            return "HEAP_WRITE";
        }
        if (looksLikeMapLookup(text)) {
            return "HEAP_LOOKUP";
        }
        if (looksLikeModeledTransform(text)) {
            return "MODEL_TRANSFORM";
        }
        if (normalizedKind.contains("constructor")) {
            return "CONSTRUCT";
        }
        if (normalizedKind.contains("accessor")
                || normalizedKind.contains("receiver_field")) {
            return "PROJECTION";
        }
        if (normalizedKind.contains("argument")
                || normalizedKind.endsWith("receiver")
                || normalizedKind.contains("caller_receiver")) {
            return "IDENTITY_BINDING";
        }
        if (normalizedKind.contains("return")) {
            return "FUNCTION_RETURN";
        }
        if (normalizedKind.contains("local_def_use")) {
            if (invoke != null && !invoke.trim().isEmpty()) {
                return "FUNCTION_RETURN";
            }
            return looksLikeComputation(unit) ? "COMPUTE" : "VALUE_PASS";
        }
        if (normalizedKind.contains("projected")) {
            return "PROJECTION";
        }
        return "UNKNOWN";
    }

    private static boolean looksLikeMapMutation(String text) {
        return looksLikeMapOperation(text, "put")
                || looksLikeMapOperation(text, "putall")
                || looksLikeMapOperation(text, "remove")
                || looksLikeMapOperation(text, "clear")
                || looksLikeMapOperation(text, "replace")
                || looksLikeMapOperation(text, "replaceall")
                || looksLikeMapOperation(text, "compute")
                || looksLikeMapOperation(text, "computeifabsent")
                || looksLikeMapOperation(text, "computeifpresent")
                || looksLikeMapOperation(text, "merge");
    }

    private static boolean looksLikeMapLookup(String text) {
        return looksLikeMapOperation(text, "get")
                || looksLikeMapOperation(text, "getordefault")
                || looksLikeMapOperation(text, "containskey")
                || looksLikeMapOperation(text, "containsvalue");
    }

    private static boolean looksLikeMapOperation(String text, String operation) {
        if (text == null || text.isEmpty()) {
            return false;
        }
        String marker = operation + "(";
        boolean namedMap = text.contains(" map." + marker)
                || text.contains(" allkeys." + marker)
                || text.contains(" keymap." + marker)
                || text.contains(" cache." + marker);
        boolean mapOwner = text.contains("<java.util.map:")
                || text.contains("<java.util.hashmap:")
                || text.contains("<java.util.linkedhashmap:")
                || text.contains("<java.util.treemap:")
                || text.contains("<java.util.concurrent.concurrentmap:")
                || text.contains("<java.util.concurrent.concurrenthashmap:");
        return namedMap || (mapOwner && (text.contains(" " + marker)
                || text.contains("." + marker)));
    }

    private static boolean looksLikeModeledTransform(String text) {
        return text.contains("stringbuilder")
                || text.contains("stringbuffer")
                || text.contains("java.lang.string: java.lang.string concat")
                || text.contains("java.lang.string: java.lang.string[] split")
                || text.contains("integer: int parseint")
                || text.contains("long: long parselong")
                || text.contains("base64")
                || text.contains(" encode")
                || text.contains(" decode")
                || text.contains("serialize")
                || text.contains("deserialize")
                || text.contains("readfields")
                || text.contains("writefields");
    }

    private static boolean looksLikeComputation(String unit) {
        String text = lower(firstNonBlank(unit, ""));
        return text.contains(" + ")
                || text.contains(" - ")
                || text.contains(" * ")
                || text.contains(" / ")
                || text.contains(" % ")
                || text.contains(" & ")
                || text.contains(" | ")
                || text.contains(" ^ ")
                || text.contains(" cmp")
                || text.contains(" new ")
                || text.startsWith("new ");
    }

    private static String stableSiteId(String method, int unitIndex, String kind) {
        if (unitIndex >= 0) {
            return method + "#u" + unitIndex;
        }
        return method + "#synthetic:" + firstNonBlank(kind, "edge");
    }

    private static Map<String, Object> summarizePlanClassifications(
            List<Map<String, Object>> plan) {
        Map<String, Object> counts = object();
        for (Map<String, Object> row : plan) {
            String classification = stringValue(row.get("classification"));
            Object previous = counts.get(classification);
            counts.put(classification, previous instanceof Number
                    ? ((Number) previous).intValue() + 1 : 1);
        }
        return counts;
    }

    private static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static int intValue(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        try {
            return Integer.parseInt(String.valueOf(value));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String lower(String value) {
        return value == null ? "" : value.toLowerCase(Locale.ROOT);
    }

    private static List<String> sortedLimited(Set<String> values, int limit) {
        List<String> sorted = new ArrayList<>(values);
        Collections.sort(sorted);
        if (sorted.size() <= limit) {
            return sorted;
        }
        return new ArrayList<>(sorted.subList(0, limit));
    }

    private static final class SymbolicPlanBuilder {
        private static final int MAX_PLAN_VALUES = 256;

        private final String method;
        private final Set<String> inputs = new LinkedHashSet<>();
        private final Set<String> defined = new LinkedHashSet<>();
        private final Set<String> outputs = new LinkedHashSet<>();
        private final Set<String> heapInputs = new LinkedHashSet<>();
        private final Set<String> environmentInputs = new LinkedHashSet<>();
        private final Set<String> guards = new LinkedHashSet<>();
        private final Set<String> exceptions = new LinkedHashSet<>();
        private final Set<String> possibleCallees = new LinkedHashSet<>();
        private final Set<String> transferKinds = new LinkedHashSet<>();
        private final Set<String> siteIds = new LinkedHashSet<>();
        private final Set<String> requiredModels = new LinkedHashSet<>();
        private final Set<String> reasons = new LinkedHashSet<>();
        private int edgeCount;

        private SymbolicPlanBuilder(String method) {
            this.method = method;
        }

        private void observe(Map<String, Object> edge, String transfer,
                             String siteId) {
            edgeCount++;
            String from = stringValue(edge.get("fromCell"));
            String to = stringValue(edge.get("toCell"));
            String unit = stringValue(edge.get("unit"));
            String invoke = stringValue(edge.get("invoke"));
            if (!from.isEmpty()) {
                inputs.add(from);
            }
            if (!to.isEmpty()) {
                outputs.add(to);
                defined.add(to);
            }
            transferKinds.add(transfer);
            siteIds.add(siteId);
            if (!invoke.isEmpty()) {
                possibleCallees.add(invoke);
            }
            if ("HEAP_READ".equals(transfer) || "HEAP_LOOKUP".equals(transfer)
                    || from.contains("#field:") || looksLikeFieldSignature(from)) {
                heapInputs.add(from);
            }
            if ("GUARD".equals(transfer)) {
                guards.add(firstNonBlank(unit, to, siteId));
                reasons.add("relevant branch guard");
            }
            if ("EXCEPTION".equals(transfer)) {
                exceptions.add(firstNonBlank(unit, to, siteId));
                reasons.add("relevant exceptional path");
            }
            if ("HEAP_WRITE".equals(transfer)) {
                reasons.add("writes coordination-relevant heap state");
            }
            if ("HEAP_LOOKUP".equals(transfer)) {
                requiredModels.add("symbolic_map_state");
                reasons.add("selects or looks up state by symbolic key");
            }
            if ("MODEL_TRANSFORM".equals(transfer)) {
                reasons.add("requires an observed region summary for the "
                        + "transformation");
                if (edge.containsKey("containerProjectionContractVersion")) {
                    requiredModels.add("symbolic_container_projection");
                    reasons.add("preserves collection elements through an "
                            + "exact Java collection API contract");
                }
            }
            if ("PROTOCOL_TRANSFER".equals(transfer)) {
                reasons.add("crosses a format or protocol boundary that "
                        + "requires region capture and runtime mapping");
            }
            if ("DYNAMIC_DISPATCH".equals(transfer)) {
                requiredModels.add("dynamic_dispatch_resolution");
                reasons.add("selects a runtime callee or receiver state");
            }
            if ("COMPUTE".equals(transfer)) {
                reasons.add("computes a new tracked value");
            }
            String lowerUnit = lower(unit);
            if (lowerUnit.contains("time.now")
                    || lowerUnit.contains("currenttimemillis")
                    || lowerUnit.contains("nanotime")) {
                environmentInputs.add("environment.now");
                reasons.add("reads symbolic time");
            }
        }

        private Map<String, Object> toRow(String id) {
            Set<String> liveIns = new LinkedHashSet<>(inputs);
            liveIns.removeAll(defined);
            for (String value : inputs) {
                if (value.contains(".param") || value.contains("@this")
                        || value.contains("#field:") || looksLikeFieldSignature(value)) {
                    liveIns.add(value);
                }
            }
            liveIns.addAll(heapInputs);
            liveIns.addAll(environmentInputs);

            String classification = classification();
            if (reasons.isEmpty()) {
                reasons.add("tracked projection is forwarded without a local semantic transform");
            }
            boolean truncated = inputs.size() > MAX_PLAN_VALUES
                    || outputs.size() > MAX_PLAN_VALUES
                    || siteIds.size() > MAX_PLAN_VALUES;
            return object(
                    "id", id,
                    "method", method,
                    "classification", classification,
                    "requiresSymbolicExecution", "SYMBOLIC_EXECUTION".equals(classification),
                    "reason", joinReasons(reasons),
                    "edgeCount", edgeCount,
                    "symbolicInputs", sortedLimited(liveIns, MAX_PLAN_VALUES),
                    "heapInputs", sortedLimited(heapInputs, MAX_PLAN_VALUES),
                    "environmentInputs", sortedLimited(environmentInputs, MAX_PLAN_VALUES),
                    "outputs", sortedLimited(outputs, MAX_PLAN_VALUES),
                    "guards", sortedLimited(guards, MAX_PLAN_VALUES),
                    "exceptions", sortedLimited(exceptions, MAX_PLAN_VALUES),
                    "transferKinds", sortedLimited(transferKinds, MAX_PLAN_VALUES),
                    "possibleCallees", sortedLimited(possibleCallees, MAX_PLAN_VALUES),
                    "runtimeObservedCallees", Collections.emptyList(),
                    "requiredModels", sortedLimited(requiredModels, MAX_PLAN_VALUES),
                    "siteIds", sortedLimited(siteIds, MAX_PLAN_VALUES),
                    "truncated", truncated,
                    "precision", "graph_directed_static_slice");
        }

        private String classification() {
            if (transferKinds.contains("COMPUTE")
                    || transferKinds.contains("GUARD")
                    || transferKinds.contains("EXCEPTION")
                    || transferKinds.contains("HEAP_WRITE")
                    || transferKinds.contains("MODEL_TRANSFORM")
                    || transferKinds.contains("PROTOCOL_TRANSFER")
                    || transferKinds.contains("CONSTRUCT")
                    || transferKinds.contains("UNKNOWN")
                    || (transferKinds.contains("HEAP_LOOKUP")
                    && (!guards.isEmpty() || !exceptions.isEmpty()))) {
                return "SYMBOLIC_EXECUTION";
            }
            if (transferKinds.contains("HEAP_LOOKUP")
                    || transferKinds.contains("DYNAMIC_DISPATCH")) {
                return "ROUTE_SUMMARY";
            }
            return "FUNCTION_PASS";
        }

        private static boolean looksLikeFieldSignature(String value) {
            return value != null && value.matches("<[^:]+:\\s+.+\\s+[^\\s()]+>");
        }

        private static String joinReasons(Set<String> values) {
            StringBuilder builder = new StringBuilder();
            for (String value : values) {
                if (builder.length() > 0) {
                    builder.append("; ");
                }
                builder.append(value);
            }
            return builder.toString();
        }
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
            writeJsonl("symbolic_execution_plan.jsonl", result.symbolicPlan);
            writeJsonl("symbolic_regions.jsonl", result.symbolicRegions);
            writeJsonl("symbolic_region_edges.jsonl", result.symbolicRegionEdges);
            writeJsonl("symbolic_models.jsonl", result.symbolicModels);
            writeJson("symbolic_coverage.json", result.symbolicCoverage);
            writeJson("automatic_derivation_boundary.json",
                    result.automaticDerivationBoundary);
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
