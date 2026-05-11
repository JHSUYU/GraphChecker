package edu.uva.liftlab.graphchecker.grey;

import soot.Body;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

public final class GreyStateProbeInstrumenter {
    private static final String RECORDER_CLASS = "org.apache.hadoop.hdfs.tracing.GreyTraceRecorder";

    public int instrument(GreyStateAnalysisResult result) {
        Map<String, SemanticEvent> eventsByKey = new LinkedHashMap<String, SemanticEvent>();
        for (SemanticEvent event : result.getEvents()) {
            eventsByKey.put(key(event.getMethod(), event.getUnit()), event);
        }
        if (eventsByKey.isEmpty()) {
            return 0;
        }

        SootClass recorder = Scene.v().forceResolve(RECORDER_CLASS, SootClass.SIGNATURES);
        RefType stringType = RefType.v("java.lang.String");
        SootMethodRef recordRef = Scene.v().makeMethodRef(
                recorder,
                "record",
                Arrays.<Type>asList(stringType, stringType, stringType, stringType),
                VoidType.v(),
                true);

        int inserted = 0;
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            if (sootClass.getName().equals(RECORDER_CLASS)
                    || sootClass.getName().startsWith("org.apache.hadoop.hdfs.tracing.")) {
                continue;
            }
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
                PatchingChain<Unit> units = body.getUnits();
                java.util.Iterator<Unit> iterator = units.snapshotIterator();
                while (iterator.hasNext()) {
                    Unit unit = iterator.next();
                    SemanticEvent event = eventsByKey.get(key(method.getSignature(), unit.toString()));
                    if (event == null || !(unit instanceof Stmt)) {
                        continue;
                    }
                    Stmt probe = Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(recordRef,
                                    Arrays.<Value>asList(
                                            StringConstant.v(event.stableId()),
                                            StringConstant.v(event.getEventType()),
                                            StringConstant.v(event.getMethod()),
                                            StringConstant.v(event.getUnit()))));
                    if (isBeforeEvent(event.getEventType())) {
                        units.insertBefore(probe, unit);
                    } else {
                        units.insertAfter(probe, unit);
                    }
                    inserted++;
                }
            }
        }
        return inserted;
    }

    private boolean isBeforeEvent(String eventType) {
        return "VALIDATE_MAP_LOOKUP".equals(eventType)
                || "RECEIVE_METADATA".equals(eventType)
                || eventType.startsWith("RECOVERY_");
    }

    private String key(String method, String unit) {
        return method + "\n" + unit;
    }
}
