package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import org.junit.Test;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.ByteType;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.Jimple;
import soot.jimple.StringConstant;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class ConcolicAtomicCarrierSelectionTest {
    private static final String INT_VALUE =
            "<java.util.concurrent.atomic.AtomicInteger: int value>";
    private static final String LONG_VALUE =
            "<java.util.concurrent.atomic.AtomicLong: long value>";

    @Test
    public void explicitFaultIsAControlRootOutsideFatalValueSlice()
            throws Exception {
        soot.G.reset();
        System.clearProperty(WireFlowCatalog.PROPERTY);
        try {
            SootClass object = type("java.lang.Object", null, false);
            SootClass string = type("java.lang.String", object, false);
            SootClass runtimeException = type("java.lang.RuntimeException",
                    object, false);
            SootMethod runtimeConstructor = constructor(runtimeException,
                    null);
            SootClass failure = type("example.RootFailure",
                    runtimeException, true);
            SootMethod failureConstructor = constructor(failure,
                    runtimeConstructor);

            SootClass debug = type(
                    "edu.uva.liftlab.graphchecker.annotation.Debug",
                    object, false);
            SootMethod marker = new SootMethod("makeSymbolicBoolean",
                    Collections.singletonList(RefType.v(string.getName())),
                    BooleanType.v(), Modifier.PUBLIC | Modifier.STATIC);
            debug.addMethod(marker);

            SootClass owner = type("example.ExplicitFaultComponent",
                    object, true);
            SootMethod target = unconditionalFailure(owner, "target",
                    failure, failureConstructor);
            SootMethod fault = explicitFaultFailure(owner, marker,
                    failure, failureConstructor);
            ExceptionTargetSite site = new ExceptionTargetSite(
                    "explicit-fault-root", owner.getName(),
                    target.getName(), "()V", target.getSignature(),
                    failure.getName(), 0);

            StaticProgram program = new SeedBackwardStaticAnalyzer(
                    new CausynthTargetContext(null, site.id, site))
                    .analyze();

            String faultCell = fault.getSignature() + "::fault";
            assertTrue(program.traceMethods.contains(fault.getSignature()));
            assertTrue(program.edges.stream().anyMatch(edge ->
                    Boolean.TRUE.equals(edge.get("explicitSymbolicFault"))
                            && fault.getSignature().equals(
                            edge.get("method"))
                            && faultCell.equals(edge.get("toCell"))));
            assertTrue(program.edges.stream().anyMatch(edge ->
                    "guard_dependency".equals(edge.get("kind"))
                            && fault.getSignature().equals(
                            edge.get("method"))
                            && faultCell.equals(edge.get("fromCell"))));

            SymbolicRegionPlanner.planSelectedSkeleton(program,
                    program.traceMethods);
            assertTrue(program.regions.stream().anyMatch(region ->
                    fault.getSignature().equals(region.get("rootMethod"))
                            && SymbolicRegionPlanner.EXPLICIT_FAULT_ENTRY
                            .equals(region.get("rootAuthority"))
                            && "EXPLICIT_FAULT_CONTEXT".equals(
                            region.get("selection"))));
        } finally {
            System.clearProperty(WireFlowCatalog.PROPERTY);
            soot.G.reset();
        }
    }

    private static ConcolicInstrumentationSelections
            .ConcolicMaterializationSelection selection(
            String owner, String name, String descriptor) throws Exception {
        JsonObject carrier = carrier(owner, name, descriptor);
        JsonArray carriers = new JsonArray();
        carriers.add(carrier);
        ConcolicInstrumentationSelections.ConcolicMaterializationSelection
                selection = new ConcolicInstrumentationSelections
                .ConcolicMaterializationSelection();
        selection.addSharedCarrierTargets(carriers, new JsonArray());
        return selection;
    }

    private static JsonObject carrier(
            String owner, String name, String descriptor) {
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "DECLARED_FIELD");
        carrier.addProperty("declaringClass", owner);
        carrier.addProperty("fieldName", name);
        carrier.addProperty("descriptor", descriptor);
        carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        carrier.add("fieldPath", new JsonArray());
        return carrier;
    }

    private static JsonObject concreteFieldRead(
            String fieldSignature, String site) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "CONCRETE");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("accessFieldSignature", fieldSignature);
        action.addProperty("staticAccessSiteId", site);
        return action;
    }

    private static SootMethod lookupTarget(
            SootClass owner, SootClass stateType, SootClass mapType,
            SootClass memberType, SootField entries, SootField value,
            SootMethod get, SootClass failure, SootMethod failureConstructor) {
        SootMethod method = new SootMethod("failWhenMissing", Arrays.asList(
                RefType.v(stateType.getName()), RefType.v("java.lang.Object")),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local state = local(body, "state", RefType.v(stateType.getName()));
        Local key = local(body, "key", RefType.v("java.lang.Object"));
        Local map = local(body, "map", RefType.v(mapType.getName()));
        Local raw = local(body, "raw", RefType.v("java.lang.Object"));
        Local member = local(body, "member", RefType.v(memberType.getName()));
        Local primitive = local(body, "primitive", IntType.v());
        Local thrown = local(body, "thrown", RefType.v(failure.getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(state,
                Jimple.v().newParameterRef((RefType) state.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(key,
                Jimple.v().newParameterRef((RefType) key.getType(), 1)));
        body.getUnits().add(Jimple.v().newAssignStmt(map,
                Jimple.v().newInstanceFieldRef(state, entries.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(raw,
                Jimple.v().newInterfaceInvokeExpr(map, get.makeRef(), key)));
        body.getUnits().add(Jimple.v().newAssignStmt(member,
                Jimple.v().newCastExpr(raw, member.getType())));
        Unit dereference = Jimple.v().newAssignStmt(primitive,
                Jimple.v().newInstanceFieldRef(member, value.makeRef()));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(member, soot.jimple.NullConstant.v()),
                dereference));
        body.getUnits().add(Jimple.v().newAssignStmt(thrown,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(thrown,
                        failureConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(thrown));
        body.getUnits().add(dereference);
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static SootMethod unconditionalFailure(
            SootClass owner, String name, SootClass failure,
            SootMethod failureConstructor) {
        SootMethod method = new SootMethod(name, Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local thrown = local(body, "targetThrown",
                RefType.v(failure.getName()));
        body.getUnits().add(Jimple.v().newAssignStmt(thrown,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(thrown,
                        failureConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(thrown));
        return method;
    }

    private static SootMethod explicitFaultFailure(
            SootClass owner, SootMethod marker, SootClass failure,
            SootMethod failureConstructor) {
        SootMethod method = new SootMethod("transport",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local fault = local(body, "fault", BooleanType.v());
        Local thrown = local(body, "faultThrown",
                RefType.v(failure.getName()));
        Unit normal = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newAssignStmt(fault,
                Jimple.v().newStaticInvokeExpr(marker.makeRef(),
                        StringConstant.v("transport-fault"))));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(fault, soot.jimple.IntConstant.v(0)),
                normal));
        body.getUnits().add(Jimple.v().newAssignStmt(thrown,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(thrown,
                        failureConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(thrown));
        body.getUnits().add(normal);
        return method;
    }

    private static SootClass type(String name, SootClass parent,
                                  boolean application) {
        SootClass result = new SootClass(name, Modifier.PUBLIC);
        if (parent != null) result.setSuperclass(parent);
        Scene.v().addClass(result);
        if (application) result.setApplicationClass();
        else result.setLibraryClass();
        return result;
    }

    private static SootMethod constructor(SootClass owner,
                                          SootMethod parent) {
        SootMethod constructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        owner.addMethod(constructor);
        if (parent != null) {
            Body body = Jimple.v().newBody(constructor);
            constructor.setActiveBody(body);
            Local self = local(body, "this", RefType.v(owner.getName()));
            body.getUnits().add(Jimple.v().newIdentityStmt(self,
                    Jimple.v().newThisRef((RefType) self.getType())));
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newSpecialInvokeExpr(self, parent.makeRef())));
            body.getUnits().add(Jimple.v().newReturnVoidStmt());
        }
        return constructor;
    }

    private static Local local(Body body, String name, soot.Type type) {
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }
}
