package edu.uva.liftlab.graphchecker.transformer;

import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import edu.uva.liftlab.graphchecker.distributedtracing.BaggagePropagation;
import edu.uva.liftlab.graphchecker.distributedtracing.HTTPPropagator;
import edu.uva.liftlab.graphchecker.generator.GraphCheckerMethodGenerator;
import edu.uva.liftlab.graphchecker.generator.LockGenerator;
import edu.uva.liftlab.graphchecker.isolation.IO.IOIsolation;
import edu.uva.liftlab.graphchecker.isolation.stateredirection.ClassFilterHelper;
import edu.uva.liftlab.graphchecker.isolation.stateredirection.StateRedirection;
import edu.uva.liftlab.graphchecker.sanitization.Sanitization;
import edu.uva.liftlab.graphchecker.util.SootUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;

import java.util.*;

import static edu.uva.liftlab.graphchecker.util.Constants.INSTRUMENTATION_SUFFIX;

public class GraphCheckerTransformer extends SceneTransformer {

    public static final PhaseInfo PHASE_INFO = new PhaseInfo("wjtp", "transformer method",
            "Transform the run method of RpcExecutor$Handler", true, false);

    private static final Logger LOG = LoggerFactory.getLogger(GraphCheckerTransformer.class);

    public static final String SET_BY_DRY_RUN = "$setByDryRun";

    private static final String TRACE_RECORDER_CLASS = "org.pilot.trace.TraceRecorder";

    public String config_file_path;

    private GraphCheckerMethodGenerator methodGenerator;

    public LockGenerator lockGenerator = new LockGenerator();

    public HTTPPropagator httpPropagator;

    public ClassFilterHelper filter;

    public static boolean isInnerClass(SootClass sootClass) {
        return sootClass.getName().contains("$");
    }

    public static boolean isLambdaClass(SootClass sootClass) {
        return sootClass.getName().contains("$lambda");
    }

    public static int ctxCount=0;

    public static int transformationCount=0;

    public GraphCheckerTransformer(String config_file_path) {
        this.config_file_path = config_file_path;
        this.filter = new ClassFilterHelper(this.config_file_path);
        methodGenerator = new GraphCheckerMethodGenerator(filter);
        this.httpPropagator = new HTTPPropagator(filter);
    }

    /**
     * Inject OpenTelemetry initialization into the static initializer of configured tracking classes.
     */
    private void transformInitClass() {
        Set<SootClass> initClasses = new HashSet<>();
        for (String str : this.filter.trackInitClasses) {
            initClasses.add(Scene.v().getSootClass(str));
        }

        for (SootClass sc : initClasses) {
            SootMethod clinit;

            if (sc.declaresMethodByName("<clinit>")) {
                clinit = sc.getMethodByName("<clinit>");
            } else {
                clinit = new SootMethod("<clinit>",
                        Collections.emptyList(),
                        VoidType.v(),
                        Modifier.STATIC);
                sc.addMethod(clinit);
                JimpleBody body = Jimple.v().newBody(clinit);
                clinit.setActiveBody(body);
                body.getUnits().add(Jimple.v().newReturnVoidStmt());
            }

            Body body = clinit.retrieveActiveBody();
            PatchingChain<Unit> units = body.getUnits();

            SootClass recorderClass = Scene.v().getSootClass(TRACE_RECORDER_CLASS);
            SootMethod initMethod = recorderClass.getMethod("void initializeOpenTelemetry()");
            InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(initMethod.makeRef());
            Unit invokeStmt = Jimple.v().newInvokeStmt(invokeExpr);

            Unit insertPoint = null;
            for (Unit unit : units) {
                if (!(unit instanceof IdentityStmt)) {
                    insertPoint = unit;
                    break;
                }
            }

            if (insertPoint != null) {
                units.insertBefore(invokeStmt, insertPoint);
            } else {
                units.insertBefore(invokeStmt, units.getLast());
            }

            body.validate();
        }
    }

    /**
     * Instrument methods with context tracking spans for pilot execution.
     */
    private void transformPilotExecution() {
        Set<SootMethod> instrumentedMethods = SootUtils.shouldInstrumentedMethods;

        for (SootMethod originalMethod : instrumentedMethods) {
            try {
                String instrumentedMethodName = originalMethod.getName() + INSTRUMENTATION_SUFFIX;
                SootClass declaringClass = originalMethod.getDeclaringClass();

                String subSignature = originalMethod.getSubSignature()
                        .replace(originalMethod.getName(), instrumentedMethodName);

                SootMethod instrumentedMethod = declaringClass.getMethodUnsafe(subSignature);

                if (instrumentedMethod != null) {
                    LOG.info("Found instrumented method: {} for original: {}",
                            instrumentedMethod.getSignature(), originalMethod.getSignature());
                } else {
                    LOG.warn("Could not find instrumented version of method: {} with suffix: {}",
                            originalMethod.getSignature(), INSTRUMENTATION_SUFFIX);
                }
            } catch (Exception e) {
                LOG.error("Failed to transform pilot execution for method {}: {}",
                        originalMethod.getSignature(), e.getMessage(), e);
            }
        }

        LOG.info("Completed context tracking transformation");
    }

    public void instrument(){

        IOIsolation.redirectAllClassesIO(filter);
        this.httpPropagator.injectCtxHooks();
        this.methodGenerator.processClasses();
        StateRedirection.redirectAllClassesStates(filter);
        for(SootClass sc: Scene.v().getApplicationClasses()){
            // Skip interfaces and phantom classes
            boolean isPilotFuncBlackListClass = filter.isBlackListPilotFuncClass(sc) && !filter.isWhiteListPilotFuncClass(sc);
            if(isPilotFuncBlackListClass && !filter.isTraceClass(sc)){
                continue;
            }
            BaggagePropagation baggagePropagation = new BaggagePropagation(sc,filter);
            baggagePropagation.propagateBaggage();
        }
        transformInitClass();
        SootUtils.getShouldInstrumentedMethodForCtxTree(filter);
        transformPilotExecution();
        Sanitization.sanitizeAllClasses();
    }


    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        LOG.info("filter.isSimpleInstrumentation: " + filter.isSimpleInstrumentation);
        if(filter.isSimpleInstrumentation){
            LOG.info("IO Classes: " + filter.ioClasses.toString());
            this.httpPropagator.injectCtxHooks();
            if(!filter.ioClasses.isEmpty()){
                IOIsolation.redirectAllClassesIO(filter);
            }
            return;
        }

        LOG.info("Complete instrumentation");
        instrument();
    }

}
