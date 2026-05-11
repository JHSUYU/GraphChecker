package edu.uva.liftlab.graphchecker.grey;

import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.ConditionExpr;
import soot.jimple.CastExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.IfStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.BriefUnitGraph;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class GreyStateConeExtractor {
    private static final String EVIDENCE_STATIC = "static";
    private static final String EVIDENCE_LOCAL_SYMBOLIC = "local_symbolic_execution";

    public GreyStateAnalysisResult extract(GreyStateSpec spec) {
        GreyStateAnalysisResult result = new GreyStateAnalysisResult();
        Set<String> fatalMaps = new LinkedHashSet<String>();
        Set<String> fatalKeys = new LinkedHashSet<String>();

        for (GreyStateSpec.FatalSeed seed : spec.getFatalSeeds()) {
            SootClass seedClass = resolveClass(seed.getClassName(), result);
            if (seedClass == null) {
                continue;
            }
            List<SootMethod> methods = methodsNamed(seedClass, seed.getMethodName());
            if (methods.isEmpty()) {
                result.addUnknown(new UnknownEdge(
                        "fatal seed method not found",
                        seed.getClassName() + "." + seed.getMethodName(),
                        "fatal predicate cannot be extracted"));
                continue;
            }
            for (SootMethod method : methods) {
                extractFatalPredicate(method, seed, result, fatalMaps, fatalKeys);
            }
        }

        for (SootClass sootClass : analysisClasses(spec)) {
            for (SootMethod method : sootClass.getMethods()) {
                if (!method.isConcrete()) {
                    continue;
                }
                try {
                    Body body = method.retrieveActiveBody();
                    extractStateWriters(method, body, fatalMaps, result);
                    extractSerialization(method, body, fatalKeys, result);
                    extractCacheAndDerive(method, body, result);
                    extractTemporalLoops(method, body, result);
                    extractRecovery(method, body, result);
                } catch (RuntimeException exception) {
                    result.addUnknown(new UnknownEdge(
                            "method body unavailable",
                            method.getSignature(),
                            exception.getMessage()));
                }
            }
        }

        if (fatalMaps.isEmpty()) {
            result.addUnknown(new UnknownEdge(
                    "no fatal map state discovered",
                    "fatal seeds",
                    "cannot build validation-state transition"));
        }
        if (fatalKeys.isEmpty()) {
            result.addUnknown(new UnknownEdge(
                    "no fatal lookup key discovered",
                    "fatal seeds",
                    "cannot build metadata flow"));
        }
        return result;
    }

    private void extractFatalPredicate(
            SootMethod method,
            GreyStateSpec.FatalSeed seed,
            GreyStateAnalysisResult result,
            Set<String> fatalMaps,
            Set<String> fatalKeys) {
        if (!method.isConcrete()) {
            result.addUnknown(new UnknownEdge(
                    "fatal seed method is not concrete",
                    method.getSignature(),
                    "fatal predicate cannot be extracted"));
            return;
        }
        Body body = method.retrieveActiveBody();
        Map<String, MapGet> mapGetsByLocal = new LinkedHashMap<String, MapGet>();
        Map<String, String> localAliases = new LinkedHashMap<String, String>();
        Map<String, String> mapAliases = new LinkedHashMap<String, String>();
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)) {
                continue;
            }
            AssignStmt assign = (AssignStmt) unit;
            if (assign.getLeftOp() instanceof Local && assign.getRightOp() instanceof CastExpr) {
                Value inner = ((CastExpr) assign.getRightOp()).getOp();
                if (inner instanceof Local) {
                    localAliases.put(((Local) assign.getLeftOp()).getName(), ((Local) inner).getName());
                }
            }
            if (assign.getLeftOp() instanceof Local && assign.getRightOp() instanceof InstanceFieldRef) {
                InstanceFieldRef fieldRef = (InstanceFieldRef) assign.getRightOp();
                if (isMapLike(fieldRef.getField().getType().toString())) {
                    mapAliases.put(((Local) assign.getLeftOp()).getName(), render(fieldRef));
                }
            }
            InvokeExpr invoke = invokeFrom(assign.getRightOp());
            if (invoke == null || !(assign.getLeftOp() instanceof Local)) {
                continue;
            }
            if ("get".equals(invoke.getMethod().getName())
                    && invoke.getArgCount() == 1
                    && invoke instanceof InstanceInvokeExpr) {
                String resultLocal = ((Local) assign.getLeftOp()).getName();
                String rawMap = render(((InstanceInvokeExpr) invoke).getBase());
                String map = mapAliases.containsKey(rawMap) ? mapAliases.get(rawMap) : rawMap;
                String key = render(invoke.getArg(0));
                mapGetsByLocal.put(resultLocal, new MapGet(map, key, unit.toString()));
            }
        }

        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof IfStmt)) {
                continue;
            }
            IfStmt ifStmt = (IfStmt) unit;
            Value condition = ifStmt.getCondition();
            if (!(condition instanceof ConditionExpr)) {
                continue;
            }
            ConditionExpr conditionExpr = (ConditionExpr) condition;
            String checkedLocal = null;
            if (conditionExpr.getOp1() instanceof Local && conditionExpr.getOp2() instanceof NullConstant) {
                checkedLocal = ((Local) conditionExpr.getOp1()).getName();
            } else if (conditionExpr.getOp2() instanceof Local && conditionExpr.getOp1() instanceof NullConstant) {
                checkedLocal = ((Local) conditionExpr.getOp2()).getName();
            }
            if (checkedLocal == null || !mapGetsByLocal.containsKey(checkedLocal)) {
                checkedLocal = resolveAlias(checkedLocal, localAliases);
                if (checkedLocal == null || !mapGetsByLocal.containsKey(checkedLocal)) {
                    continue;
                }
            }
            if (!guardCanReachThrow(body, ifStmt, seed.getExceptionClass())) {
                result.addUnknown(new UnknownEdge(
                        "map lookup null guard not tied to configured exception",
                        method.getSignature(),
                        "validation predicate may be non-fatal"));
            }
            MapGet mapGet = mapGetsByLocal.get(checkedLocal);
            fatalMaps.add(mapGet.map);
            fatalKeys.add(mapGet.key);
            Map<String, String> attrs = attrs(
                    "map", mapGet.map,
                    "key", mapGet.key,
                    "resultLocal", checkedLocal,
                    "predicate", "select(" + mapGet.map + ", " + mapGet.key + ") == null",
                    "exception", seed.getExceptionClass());
            result.addEvent(new SemanticEvent(
                    "VALIDATE_MAP_LOOKUP",
                    method.getSignature(),
                    unit.toString(),
                    attrs));
            result.addSummary(new TransitionSummary(
                    method.getSignature(),
                    "fatal_predicate",
                    "fatal := select(" + mapGet.map + ", " + mapGet.key + ") == null",
                    Arrays.asList(EVIDENCE_STATIC)));
        }
    }

    private boolean guardCanReachThrow(Body body, IfStmt ifStmt, String exceptionClass) {
        if (exceptionClass == null || exceptionClass.trim().isEmpty()) {
            return true;
        }
        Unit cursor = ifStmt.getTarget();
        int budget = 12;
        while (cursor != null && budget-- > 0) {
            if (cursor instanceof ThrowStmt) {
                return true;
            }
            if (cursor instanceof Stmt && ((Stmt) cursor).containsInvokeExpr()) {
                InvokeExpr invoke = ((Stmt) cursor).getInvokeExpr();
                if (invoke.getMethod().getSignature().contains(exceptionClass)
                        || invoke.getMethod().getDeclaringClass().getName().equals(exceptionClass)) {
                    return true;
                }
            }
            cursor = body.getUnits().getSuccOf(cursor);
        }
        return false;
    }

    private void extractStateWriters(
            SootMethod method,
            Body body,
            Set<String> fatalMaps,
            GreyStateAnalysisResult result) {
        if (fatalMaps.isEmpty()) {
            return;
        }
        IteratorAliasTracker iteratorAliases = new IteratorAliasTracker(fatalMaps);
        LocalFacts facts = LocalFacts.from(body);
        Map<String, String> mapAliases = new LinkedHashMap<String, String>();
        String iteratedFatalMap = findIteratedFatalMap(body, fatalMaps);
        boolean wroteFatalMap = false;
        Set<String> externalSources = new LinkedHashSet<String>();
        for (Unit unit : body.getUnits()) {
            if (unit instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) unit;
                if (assign.getLeftOp() instanceof Local && assign.getRightOp() instanceof InstanceFieldRef) {
                    InstanceFieldRef fieldRef = (InstanceFieldRef) assign.getRightOp();
                    if (isMapLike(fieldRef.getField().getType().toString()) || maybeFatalMap(fieldRef.getField().getName(), fatalMaps)) {
                        mapAliases.put(((Local) assign.getLeftOp()).getName(), fieldRef.getField().getName());
                    }
                }
            }
            iteratorAliases.observe(unit);
            if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            if (!(invoke instanceof InstanceInvokeExpr)) {
                continue;
            }
            String methodName = invoke.getMethod().getName();
            String rawBase = render(((InstanceInvokeExpr) invoke).getBase());
            String base = mapAliases.containsKey(rawBase) ? mapAliases.get(rawBase) : rawBase;
            if ("put".equals(methodName) && invoke.getArgCount() == 2 && maybeFatalMap(base, fatalMaps)) {
                wroteFatalMap = true;
                Set<String> keyDeps = facts.dependenciesOf(invoke.getArg(0));
                Set<String> valueDeps = facts.dependenciesOf(invoke.getArg(1));
                externalSources.addAll(externalDependencies(keyDeps));
                externalSources.addAll(externalDependencies(valueDeps));
                result.addEvent(new SemanticEvent(
                        "MAP_PUT",
                        method.getSignature(),
                        unit.toString(),
                        attrs("map", base,
                                "key", render(invoke.getArg(0)),
                                "value", render(invoke.getArg(1)),
                                "keyDeps", keyDeps.toString(),
                                "valueDeps", valueDeps.toString())));
                continue;
            }
            if ("remove".equals(methodName) && invoke.getArgCount() == 1 && maybeFatalMap(base, fatalMaps)) {
                wroteFatalMap = true;
                Set<String> keyDeps = facts.dependenciesOf(invoke.getArg(0));
                externalSources.addAll(externalDependencies(keyDeps));
                result.addEvent(new SemanticEvent(
                        "MAP_REMOVE",
                        method.getSignature(),
                        unit.toString(),
                        attrs("map", base, "key", render(invoke.getArg(0)), "keyDeps", keyDeps.toString())));
                continue;
            }
            if ("remove".equals(methodName) && invoke.getArgCount() == 0) {
                String map = iteratorAliases.mapForIteratorBase(base);
                if (map == null) {
                    map = iteratedFatalMap;
                }
                if (map != null) {
                    wroteFatalMap = true;
                    result.addEvent(new SemanticEvent(
                            "MAP_REMOVE",
                            method.getSignature(),
                            unit.toString(),
                            attrs("map", map, "key", "iterator.currentKey")));
                }
            }
        }
        if (wroteFatalMap && !externalSources.isEmpty()) {
            result.addEvent(new SemanticEvent(
                    "PROPAGATION_IMPORT",
                    method.getSignature(),
                    method.getName(),
                    attrs("state", fatalMaps.toString(),
                            "source", externalSources.toString(),
                            "recognizer", "fatal-state-write-from-external-input")));
        }
    }

    private void extractSerialization(
            SootMethod method,
            Body body,
            Set<String> fatalKeys,
            GreyStateAnalysisResult result) {
        boolean hasSplit = false;
        boolean hasParseInt = false;
        boolean hasBase64Decode = false;
        boolean hasBase64Encode = false;
        boolean returnsString = "java.lang.String".equals(method.getReturnType().toString());
        Set<String> fieldReads = new LinkedHashSet<String>();
        SerializationSummary serialization = SerializationSummary.from(body);

        for (Unit unit : body.getUnits()) {
            if (unit instanceof AssignStmt) {
                collectFieldReads(((AssignStmt) unit).getRightOp(), fieldReads);
            }
            if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            String name = invoke.getMethod().getName();
            String owner = invoke.getMethod().getDeclaringClass().getName();
            hasSplit |= "split".equals(name);
            hasParseInt |= "parseInt".equals(name);
            hasBase64Decode |= owner.toLowerCase().contains("base64") && name.toLowerCase().contains("decode");
            hasBase64Encode |= owner.toLowerCase().contains("base64") && name.toLowerCase().contains("encode");
            for (Value arg : invoke.getArgs()) {
                collectFieldReads(arg, fieldReads);
            }
        }

        if (hasSplit && hasParseInt) {
            result.addEvent(new SemanticEvent(
                    "RECEIVE_METADATA",
                    method.getSignature(),
                    method.getName(),
                    attrs("decoder", "split/parse",
                            "delimiter", serialization.decodeDelimiter(),
                            "parsedIndex", serialization.parsedIndex(),
                            "base64Decode", Boolean.toString(hasBase64Decode))));
        }
        if (returnsString && looksLikeMetadataEncoder(method, fieldReads, hasBase64Encode)) {
            result.addEvent(new SemanticEvent(
                    "SEND_METADATA",
                    method.getSignature(),
                    method.getName(),
                    attrs("encoder", "string-return",
                            "components", serialization.encodedComponents().toString(),
                            "delimiter", serialization.encodeDelimiter(),
                            "fields", fieldReads.toString(),
                            "base64Encode", Boolean.toString(hasBase64Encode))));
        }
    }

    private void extractCacheAndDerive(
            SootMethod method,
            Body body,
            GreyStateAnalysisResult result) {
        String returnType = method.getReturnType().toString();
        boolean returnsReferenceMetadata = isReferenceMetadataType(returnType);
        boolean sawMetadataCtor = false;
        boolean sawTime = false;
        Set<String> fieldReads = new LinkedHashSet<String>();
        Set<String> fieldWrites = new LinkedHashSet<String>();
        Set<String> cacheFields = new LinkedHashSet<String>();
        Map<String, Unit> fieldWriteUnits = new LinkedHashMap<String, Unit>();

        for (Unit unit : body.getUnits()) {
            if (unit instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) unit;
                collectFieldReads(assign.getRightOp(), fieldReads);
                if (assign.getLeftOp() instanceof InstanceFieldRef) {
                    InstanceFieldRef fieldRef = (InstanceFieldRef) assign.getLeftOp();
                    String field = fieldRef.getField().getName();
                    fieldWrites.add(field);
                    fieldWriteUnits.put(field, unit);
                    if (fieldRef.getField().getType().toString().equals(returnType)) {
                        cacheFields.add(field);
                    }
                }
            }
            if (!(unit instanceof Stmt)) {
                continue;
            }
            Stmt stmt = (Stmt) unit;
            if (stmt instanceof ReturnStmt) {
                collectFieldReads(((ReturnStmt) stmt).getOp(), fieldReads);
            }
            if (stmt.containsInvokeExpr()) {
                InvokeExpr invoke = stmt.getInvokeExpr();
                String owner = invoke.getMethod().getDeclaringClass().getName();
                sawTime |= owner.endsWith(".Time") || owner.equals("org.apache.hadoop.util.Time");
                if (invoke instanceof SpecialInvokeExpr
                        && "<init>".equals(invoke.getMethod().getName())
                        && (owner.equals(returnType) || owner.endsWith(simpleName(returnType)))) {
                    sawMetadataCtor = true;
                    result.addEvent(new SemanticEvent(
                            "DERIVE_METADATA",
                            method.getSignature(),
                            unit.toString(),
                            attrs("metadataType", owner, "args", renderArgs(invoke))));
                }
            }
        }

        for (String field : fieldReads) {
            if (cacheFields.contains(field)) {
                result.addEvent(new SemanticEvent(
                        "CACHE_GET",
                        method.getSignature(),
                        method.getName(),
                        attrs("field", field)));
            }
        }

        if (returnsReferenceMetadata && !cacheFields.isEmpty()) {
            String cacheField = cacheFields.iterator().next();
            result.addEvent(new SemanticEvent(
                    "CACHE_PUT",
                    method.getSignature(),
                    fieldWriteUnits.get(cacheField).toString(),
                    attrs("field", cacheField,
                            "value", "derived " + returnType,
                            "metadataType", returnType)));
            String refreshGuard = guardToReach(body, fieldWriteUnits.get(cacheField));
            boolean hasValidityGuard = hasNonInitializationValidityGuard(refreshGuard);
            String formula = "cachedMetadata' = ite(" + refreshGuard
                    + ", deriveMetadata(componentState, now), cachedMetadata)";
            result.addSummary(new TransitionSummary(
                    method.getSignature(),
                    "cache_transformer",
                    formula,
                    Arrays.asList(EVIDENCE_STATIC, EVIDENCE_LOCAL_SYMBOLIC)));
            result.addEvent(new SemanticEvent(
                    hasValidityGuard ? "CACHE_REFRESH_ON_VALIDITY_GUARD" : "CACHE_REUSE_WITHOUT_EXPIRY_CHECK",
                    method.getSignature(),
                    method.getName(),
                    attrs("field", cacheField, "metadataType", returnType, "guard", refreshGuard)));
            if (hasValidityGuard) {
                result.addEvent(new SemanticEvent(
                        "CACHE_REFRESH_ON_EXPIRY",
                        method.getSignature(),
                        method.getName(),
                        attrs("field", cacheField,
                                "metadataType", returnType,
                                "guard", refreshGuard,
                                "compatibilityAlias", "CACHE_REFRESH_ON_VALIDITY_GUARD")));
            }
        }
        if (sawMetadataCtor) {
            result.addSummary(new TransitionSummary(
                    method.getSignature(),
                    "derive_metadata",
                    "metadata := new " + returnType + "(componentState, time, arguments)",
                    Arrays.asList(EVIDENCE_STATIC)));
        }
        if (sawTime && returnsReferenceMetadata) {
            result.addEvent(new SemanticEvent(
                    "TEMPORAL_GUARD",
                    method.getSignature(),
                    method.getName(),
                    attrs("timeSource", "Time.now")));
        }
    }

    private void extractTemporalLoops(
            SootMethod method,
            Body body,
            GreyStateAnalysisResult result) {
        boolean hasBackEdge = false;
        boolean sleeps = false;
        boolean importsKeys = false;
        List<Unit> units = new ArrayList<Unit>();
        for (Unit unit : body.getUnits()) {
            units.add(unit);
        }
        Map<Unit, Integer> index = new LinkedHashMap<Unit, Integer>();
        for (int i = 0; i < units.size(); i++) {
            index.put(units.get(i), i);
        }
        for (Unit unit : units) {
            if (unit instanceof IfStmt) {
                Integer from = index.get(unit);
                Integer to = index.get(((IfStmt) unit).getTarget());
                hasBackEdge |= from != null && to != null && to <= from;
            }
            if (unit instanceof GotoStmt) {
                Integer from = index.get(unit);
                Integer to = index.get(((GotoStmt) unit).getTarget());
                hasBackEdge |= from != null && to != null && to <= from;
            }
            if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()) {
                InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
                sleeps |= "sleep".equals(invoke.getMethod().getName())
                        && invoke.getMethod().getDeclaringClass().getName().equals("java.lang.Thread");
                importsKeys |= "addKeys".equals(invoke.getMethod().getName())
                        || "getBlockKeys".equals(invoke.getMethod().getName());
            }
        }
        if (hasBackEdge && (sleeps || importsKeys)) {
            result.addEvent(new SemanticEvent(
                    "PERIODIC_TRANSITION",
                    method.getSignature(),
                    method.getName(),
                    attrs("hasSleep", Boolean.toString(sleeps), "importsKeys", Boolean.toString(importsKeys))));
            result.addSummary(new TransitionSummary(
                    method.getSignature(),
                    "loop_lift",
                    "for i in 0..k: maybe_periodic_sync_i => transition_i",
                    Arrays.asList(EVIDENCE_STATIC)));
        }
    }

    private void extractRecovery(SootMethod method, Body body, GreyStateAnalysisResult result) {
        for (Trap trap : body.getTraps()) {
            RecoveryScan scan = scanHandler(body, trap.getHandlerUnit());
            if (scan.clearsKey || scan.retries) {
                result.addEvent(new SemanticEvent(
                        "RECOVERY_CLEAR_OR_RETRY",
                        method.getSignature(),
                        trap.getHandlerUnit().toString(),
                        attrs("exception", trap.getException().getName(),
                                "clearsKey", Boolean.toString(scan.clearsKey),
                                "retries", Boolean.toString(scan.retries))));
            } else if (scan.logsOrMarksFailure || scan.handlesRelevantException()) {
                result.addEvent(new SemanticEvent(
                        "RECOVERY_NO_REPAIR",
                        method.getSignature(),
                        trap.getHandlerUnit().toString(),
                        attrs("exception", trap.getException().getName(),
                                "clearsKey", "false",
                                "retries", "false")));
            }
        }
    }

    private RecoveryScan scanHandler(Body body, Unit handlerStart) {
        RecoveryScan scan = new RecoveryScan();
        Unit cursor = handlerStart;
        int budget = 80;
        while (cursor != null && budget-- > 0) {
            String text = cursor.toString();
            scan.mentionsInvalidEncryptionKey |= text.contains("InvalidEncryptionKeyException");
            if (cursor instanceof Stmt && ((Stmt) cursor).containsInvokeExpr()) {
                InvokeExpr invoke = ((Stmt) cursor).getInvokeExpr();
                String name = invoke.getMethod().getName();
                String lower = name.toLowerCase();
                scan.clearsKey |= lower.contains("clear") && lower.contains("encryption");
                scan.retries |= lower.contains("retry") || text.toLowerCase().contains("retry");
                scan.logsOrMarksFailure |= lower.contains("warn")
                        || lower.contains("sethasfailure")
                        || lower.contains("activatedelay")
                        || lower.contains("print");
            }
            if (cursor instanceof ReturnStmt || cursor.toString().startsWith("return")) {
                break;
            }
            cursor = body.getUnits().getSuccOf(cursor);
        }
        return scan;
    }

    private static final class RecoveryScan {
        private boolean mentionsInvalidEncryptionKey;
        private boolean clearsKey;
        private boolean retries;
        private boolean logsOrMarksFailure;

        private boolean handlesRelevantException() {
            return mentionsInvalidEncryptionKey || logsOrMarksFailure;
        }
    }

    private List<SootClass> analysisClasses(GreyStateSpec spec) {
        List<SootClass> classes = new ArrayList<SootClass>();
        if (!spec.getAnalysisClasses().isEmpty()) {
            Set<String> added = new LinkedHashSet<String>();
            for (String className : spec.getAnalysisClasses()) {
                SootClass sootClass = resolveClass(className, null);
                if (sootClass != null && added.add(sootClass.getName())) {
                    classes.add(sootClass);
                }
                for (SootClass nested : resolveNestedClasses(className)) {
                    if (added.add(nested.getName())) {
                        classes.add(nested);
                    }
                }
            }
            return classes;
        }
        classes.addAll(Scene.v().getApplicationClasses());
        return classes;
    }

    private List<SootClass> resolveNestedClasses(String outerClassName) {
        List<SootClass> nestedClasses = new ArrayList<SootClass>();
        String sootClassPath = Scene.v().getSootClassPath();
        if (sootClassPath == null || sootClassPath.trim().isEmpty()) {
            return nestedClasses;
        }
        String[] roots = sootClassPath.split(File.pathSeparator);
        Set<String> seen = new LinkedHashSet<String>();
        for (String root : roots) {
            File rootDir = new File(root);
            if (!rootDir.isDirectory()) {
                continue;
            }
            File packageDir = new File(rootDir, packagePath(outerClassName));
            File[] files = packageDir.listFiles();
            if (files == null) {
                continue;
            }
            String outerSimple = simpleName(outerClassName);
            for (File file : files) {
                String name = file.getName();
                if (!name.startsWith(outerSimple + "$") || !name.endsWith(".class")) {
                    continue;
                }
                String className = packageName(outerClassName) + "."
                        + name.substring(0, name.length() - ".class".length());
                if (!seen.add(className)) {
                    continue;
                }
                SootClass nested = resolveClass(className, null);
                if (nested != null) {
                    nestedClasses.add(nested);
                }
            }
        }
        return nestedClasses;
    }

    private String packagePath(String className) {
        String packageName = packageName(className);
        return packageName.replace('.', File.separatorChar);
    }

    private String packageName(String className) {
        int index = className.lastIndexOf('.');
        return index >= 0 ? className.substring(0, index) : "";
    }

    private String simpleName(String className) {
        int index = className.lastIndexOf('.');
        return index >= 0 ? className.substring(index + 1) : className;
    }

    private static boolean isMapLike(String typeName) {
        return typeName != null && (typeName.contains("java.util.Map")
                || typeName.contains("ConcurrentMap")
                || typeName.contains("HashMap")
                || typeName.contains("TreeMap"));
    }

    private static boolean isReferenceMetadataType(String typeName) {
        if (typeName == null || typeName.trim().isEmpty()) {
            return false;
        }
        return !typeName.equals("void")
                && !typeName.equals("boolean")
                && !typeName.equals("byte")
                && !typeName.equals("short")
                && !typeName.equals("char")
                && !typeName.equals("int")
                && !typeName.equals("long")
                && !typeName.equals("float")
                && !typeName.equals("double")
                && !typeName.startsWith("java.lang.String");
    }

    private static Set<String> externalDependencies(Set<String> dependencies) {
        Set<String> external = new LinkedHashSet<String>();
        for (String dependency : dependencies) {
            if (dependency.startsWith("param")
                    || dependency.startsWith("invoke:")
                    || dependency.startsWith("static:")
                    || dependency.startsWith("field:param")) {
                external.add(dependency);
            }
        }
        return external;
    }

    private String guardToReach(Body body, Unit target) {
        if (target == null) {
            return "true";
        }
        BriefUnitGraph graph = new BriefUnitGraph(body);
        List<String> pathConditions = new ArrayList<String>();
        for (Unit head : graph.getHeads()) {
            collectPathConditions(graph, head, target, new ArrayList<String>(),
                    pathConditions, new HashSet<String>(), 0);
        }
        if (pathConditions.isEmpty()) {
            return "true";
        }
        List<String> normalized = new ArrayList<String>(new LinkedHashSet<String>(pathConditions));
        if (normalized.size() == 1) {
            return normalized.get(0);
        }
        return "(" + join(") || (", normalized) + ")";
    }

    private void collectPathConditions(BriefUnitGraph graph, Unit current, Unit target,
            List<String> conditions, List<String> results, Set<String> seen, int depth) {
        if (current == null || depth > 160 || results.size() > 32) {
            return;
        }
        String state = System.identityHashCode(current) + ":" + conditions.toString();
        if (!seen.add(state)) {
            return;
        }
        if (current.equals(target)) {
            results.add(conditions.isEmpty() ? "true" : join(" && ", conditions));
            return;
        }
        if (current instanceof ReturnStmt || current instanceof ThrowStmt) {
            return;
        }
        List<Unit> successors = graph.getSuccsOf(current);
        if (current instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) current;
            String condition = render(ifStmt.getCondition());
            for (Unit successor : successors) {
                List<String> next = new ArrayList<String>(conditions);
                if (successor.equals(ifStmt.getTarget())) {
                    next.add(condition);
                } else {
                    next.add("!(" + condition + ")");
                }
                collectPathConditions(graph, successor, target, next, results,
                        new HashSet<String>(seen), depth + 1);
            }
            return;
        }
        for (Unit successor : successors) {
            collectPathConditions(graph, successor, target, conditions, results,
                    new HashSet<String>(seen), depth + 1);
        }
    }

    private static boolean hasNonInitializationValidityGuard(String guard) {
        if (guard == null) {
            return false;
        }
        String compact = guard.replace(" ", "");
        String withoutNullChecks = compact
                .replace("==null", "")
                .replace("!=null", "")
                .replace("null==", "")
                .replace("null!=", "");
        return withoutNullChecks.contains("<")
                || withoutNullChecks.contains(">")
                || withoutNullChecks.contains("invoke:")
                || withoutNullChecks.contains(".");
    }

    private static String join(String delimiter, List<String> values) {
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < values.size(); i++) {
            if (i > 0) {
                out.append(delimiter);
            }
            out.append(values.get(i));
        }
        return out.toString();
    }

    private String findIteratedFatalMap(Body body, Set<String> fatalMaps) {
        Set<String> mapLocals = new LinkedHashSet<String>();
        for (Unit unit : body.getUnits()) {
            if (unit instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) unit;
                if (assign.getLeftOp() instanceof Local && assign.getRightOp() instanceof InstanceFieldRef) {
                    InstanceFieldRef fieldRef = (InstanceFieldRef) assign.getRightOp();
                    if (maybeFatalMap(fieldRef.getField().getName(), fatalMaps)
                            || maybeFatalMap(render(fieldRef), fatalMaps)) {
                        mapLocals.add(((Local) assign.getLeftOp()).getName());
                    }
                }
            }
        }
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            if (!(invoke instanceof InstanceInvokeExpr)) {
                continue;
            }
            String name = invoke.getMethod().getName();
            if (!"entrySet".equals(name) && !"values".equals(name)) {
                continue;
            }
            String base = render(((InstanceInvokeExpr) invoke).getBase());
            if (mapLocals.contains(base)) {
                return base;
            }
            if (maybeFatalMap(base, fatalMaps)) {
                return base;
            }
        }
        return null;
    }

    private boolean looksLikeMetadataEncoder(SootMethod method, Set<String> fieldReads, boolean hasBase64Encode) {
        String name = method.getName().toLowerCase();
        if (name.contains("username") || name.contains("userName".toLowerCase())) {
            return true;
        }
        if (hasBase64Encode) {
            return true;
        }
        for (String field : fieldReads) {
            String lower = field.toLowerCase();
            if (lower.equals("keyid") || lower.equals("nonce") || lower.equals("blockpoolid")
                    || lower.equals("encryptionkey") || lower.equals("expirydate")) {
                return true;
            }
        }
        return false;
    }

    private SootClass resolveClass(String className, GreyStateAnalysisResult result) {
        try {
            SootClass sootClass = Scene.v().forceResolve(className, SootClass.BODIES);
            sootClass.setApplicationClass();
            return sootClass;
        } catch (RuntimeException exception) {
            if (result != null) {
                result.addUnknown(new UnknownEdge(
                        "class not resolved",
                        className,
                        exception.getMessage()));
            }
            return null;
        }
    }

    private List<SootMethod> methodsNamed(SootClass sootClass, String methodName) {
        List<SootMethod> methods = new ArrayList<SootMethod>();
        for (SootMethod method : sootClass.getMethods()) {
            if (method.getName().equals(methodName)) {
                methods.add(method);
            }
        }
        return methods;
    }

    private static boolean maybeFatalMap(String base, Set<String> fatalMaps) {
        if (fatalMaps.contains(base)) {
            return true;
        }
        for (String map : fatalMaps) {
            if (base.endsWith("." + map) || map.endsWith("." + base)) {
                return true;
            }
            String baseField = fieldNameFromRenderedRef(base);
            String mapField = fieldNameFromRenderedRef(map);
            if (baseField != null && baseField.equals(mapField)) {
                return true;
            }
        }
        return false;
    }

    private static String fieldNameFromRenderedRef(String rendered) {
        if (rendered == null || rendered.trim().isEmpty()) {
            return null;
        }
        int angle = rendered.lastIndexOf('>');
        int space = rendered.lastIndexOf(' ', angle >= 0 ? angle : rendered.length() - 1);
        if (angle > space && space >= 0) {
            return rendered.substring(space + 1, angle);
        }
        int dot = rendered.lastIndexOf('.');
        if (dot >= 0 && dot + 1 < rendered.length()) {
            return rendered.substring(dot + 1);
        }
        if (rendered.indexOf(' ') < 0 && rendered.indexOf('<') < 0 && rendered.indexOf('>') < 0) {
            return rendered;
        }
        return null;
    }

    private static String resolveAlias(String local, Map<String, String> aliases) {
        String current = local;
        Set<String> seen = new LinkedHashSet<String>();
        while (current != null && aliases.containsKey(current) && seen.add(current)) {
            current = aliases.get(current);
        }
        return current;
    }

    private static void collectFieldReads(Value value, Set<String> fieldReads) {
        if (value instanceof InstanceFieldRef) {
            fieldReads.add(((InstanceFieldRef) value).getField().getName());
            return;
        }
        if (value instanceof FieldRef) {
            fieldReads.add(((FieldRef) value).getField().getName());
            return;
        }
        if (value instanceof InvokeExpr) {
            InvokeExpr invoke = (InvokeExpr) value;
            for (Value arg : invoke.getArgs()) {
                collectFieldReads(arg, fieldReads);
            }
            if (invoke instanceof InstanceInvokeExpr) {
                collectFieldReads(((InstanceInvokeExpr) invoke).getBase(), fieldReads);
            }
        }
    }

    private static InvokeExpr invokeFrom(Value value) {
        return value instanceof InvokeExpr ? (InvokeExpr) value : null;
    }

    private static String renderArgs(InvokeExpr invoke) {
        List<String> args = new ArrayList<String>();
        for (Value arg : invoke.getArgs()) {
            args.add(render(arg));
        }
        return args.toString();
    }

    private static String render(Value value) {
        if (value == null) {
            return "null";
        }
        if (value instanceof InstanceFieldRef) {
            InstanceFieldRef fieldRef = (InstanceFieldRef) value;
            return render(fieldRef.getBase()) + "." + fieldRef.getField().getName();
        }
        if (value instanceof FieldRef) {
            return ((FieldRef) value).getField().getName();
        }
        if (value instanceof ParameterRef) {
            return "param" + ((ParameterRef) value).getIndex();
        }
        if (value instanceof ArrayRef) {
            ArrayRef arrayRef = (ArrayRef) value;
            return render(arrayRef.getBase()) + "[" + render(arrayRef.getIndex()) + "]";
        }
        if (value instanceof StringConstant) {
            return ((StringConstant) value).value;
        }
        if (value instanceof NewExpr) {
            return "new " + value.getType();
        }
        return value.toString();
    }

    private static Map<String, String> attrs(String... pairs) {
        Map<String, String> map = new LinkedHashMap<String, String>();
        for (int i = 0; i + 1 < pairs.length; i += 2) {
            map.put(pairs[i], pairs[i + 1]);
        }
        return map;
    }

    private static final class MapGet {
        private final String map;
        private final String key;
        @SuppressWarnings("unused")
        private final String unit;

        private MapGet(String map, String key, String unit) {
            this.map = map;
            this.key = key;
            this.unit = unit;
        }
    }

    private static final class LocalFacts {
        private final Map<String, Set<String>> dependencies = new LinkedHashMap<String, Set<String>>();

        static LocalFacts from(Body body) {
            LocalFacts facts = new LocalFacts();
            for (Unit unit : body.getUnits()) {
                if (unit instanceof IdentityStmt) {
                    IdentityStmt identity = (IdentityStmt) unit;
                    if (identity.getLeftOp() instanceof Local) {
                        facts.dependencies.put(((Local) identity.getLeftOp()).getName(),
                                facts.directDependencies(identity.getRightOp()));
                    }
                    continue;
                }
                if (unit instanceof DefinitionStmt) {
                    DefinitionStmt definition = (DefinitionStmt) unit;
                    if (definition.getLeftOp() instanceof Local) {
                        facts.dependencies.put(((Local) definition.getLeftOp()).getName(),
                                facts.dependenciesOf(definition.getRightOp()));
                    }
                }
            }
            return facts;
        }

        Set<String> dependenciesOf(Value value) {
            Set<String> out = new LinkedHashSet<String>();
            if (value == null) {
                return out;
            }
            if (value instanceof Local) {
                String local = ((Local) value).getName();
                if (dependencies.containsKey(local)) {
                    out.addAll(dependencies.get(local));
                } else {
                    out.add("local:" + local);
                }
                return out;
            }
            out.addAll(directDependencies(value));
            if (value instanceof ArrayRef) {
                ArrayRef arrayRef = (ArrayRef) value;
                out.addAll(dependenciesOf(arrayRef.getBase()));
                out.addAll(dependenciesOf(arrayRef.getIndex()));
            } else if (value instanceof InstanceFieldRef) {
                InstanceFieldRef fieldRef = (InstanceFieldRef) value;
                out.add("field:" + fieldRef.getField().getName());
                out.addAll(prefix("field:", dependenciesOf(fieldRef.getBase())));
            } else if (value instanceof InvokeExpr) {
                InvokeExpr invoke = (InvokeExpr) value;
                out.add("invoke:" + invoke.getMethod().getSignature());
                for (Value arg : invoke.getArgs()) {
                    out.addAll(dependenciesOf(arg));
                }
                if (invoke instanceof InstanceInvokeExpr) {
                    out.addAll(dependenciesOf(((InstanceInvokeExpr) invoke).getBase()));
                }
            }
            return out;
        }

        private Set<String> directDependencies(Value value) {
            Set<String> out = new LinkedHashSet<String>();
            if (value instanceof ParameterRef) {
                out.add("param" + ((ParameterRef) value).getIndex());
            } else if (value instanceof FieldRef) {
                out.add("field:" + ((FieldRef) value).getField().getName());
            } else if (value instanceof StringConstant) {
                out.add("constant:string");
            } else if (value instanceof NullConstant) {
                out.add("constant:null");
            }
            return out;
        }

        private Set<String> prefix(String prefix, Set<String> values) {
            Set<String> out = new LinkedHashSet<String>();
            for (String value : values) {
                out.add(prefix + value);
            }
            return out;
        }
    }

    private static final class SerializationSummary {
        private final List<String> encodedComponents = new ArrayList<String>();
        private String encodeDelimiter = "unknown";
        private String decodeDelimiter = "unknown";
        private String parsedIndex = "unknown";

        static SerializationSummary from(Body body) {
            SerializationSummary summary = new SerializationSummary();
            LocalFacts facts = LocalFacts.from(body);
            for (Unit unit : body.getUnits()) {
                if (!(unit instanceof Stmt)) {
                    continue;
                }
                Stmt stmt = (Stmt) unit;
                if (!stmt.containsInvokeExpr()) {
                    continue;
                }
                InvokeExpr invoke = stmt.getInvokeExpr();
                String name = invoke.getMethod().getName();
                String owner = invoke.getMethod().getDeclaringClass().getName();
                if ("append".equals(name) && invoke.getArgCount() == 1
                        && owner.equals("java.lang.StringBuilder")) {
                    Value arg = invoke.getArg(0);
                    if (arg instanceof StringConstant) {
                        String value = ((StringConstant) arg).value;
                        if (!value.isEmpty()) {
                            summary.encodeDelimiter = value;
                        }
                    } else {
                        summary.encodedComponents.add(render(arg)
                                + " deps=" + facts.dependenciesOf(arg));
                    }
                }
                if ("split".equals(name) && invoke.getArgCount() >= 1
                        && invoke.getArg(0) instanceof StringConstant) {
                    summary.decodeDelimiter = ((StringConstant) invoke.getArg(0)).value;
                }
                if ("parseInt".equals(name) && invoke.getArgCount() >= 1) {
                    Value arg = invoke.getArg(0);
                    if (arg instanceof ArrayRef) {
                        summary.parsedIndex = render(((ArrayRef) arg).getIndex());
                    } else {
                        summary.parsedIndex = render(arg);
                    }
                }
            }
            return summary;
        }

        List<String> encodedComponents() {
            return Collections.unmodifiableList(encodedComponents);
        }

        String encodeDelimiter() {
            return encodeDelimiter;
        }

        String decodeDelimiter() {
            return decodeDelimiter;
        }

        String parsedIndex() {
            return parsedIndex;
        }
    }

    private static final class IteratorAliasTracker {
        private final Set<String> fatalMaps;
        private final Map<String, String> collectionToMap = new LinkedHashMap<String, String>();
        private final Map<String, String> iteratorToMap = new LinkedHashMap<String, String>();

        private IteratorAliasTracker(Set<String> fatalMaps) {
            this.fatalMaps = fatalMaps;
        }

        void observe(Unit unit) {
            if (!(unit instanceof AssignStmt)) {
                return;
            }
            AssignStmt assign = (AssignStmt) unit;
            if (!(assign.getLeftOp() instanceof Local)) {
                return;
            }
            InvokeExpr invoke = invokeFrom(assign.getRightOp());
            if (invoke == null || !(invoke instanceof InstanceInvokeExpr)) {
                return;
            }
            String left = ((Local) assign.getLeftOp()).getName();
            String name = invoke.getMethod().getName();
            String base = render(((InstanceInvokeExpr) invoke).getBase());
            if (("values".equals(name) || "entrySet".equals(name)) && maybeFatalMap(base, fatalMaps)) {
                collectionToMap.put(left, base);
                return;
            }
            if ("iterator".equals(name) && collectionToMap.containsKey(base)) {
                iteratorToMap.put(left, collectionToMap.get(base));
            }
        }

        String mapForIteratorBase(String base) {
            return iteratorToMap.get(base);
        }
    }
}
