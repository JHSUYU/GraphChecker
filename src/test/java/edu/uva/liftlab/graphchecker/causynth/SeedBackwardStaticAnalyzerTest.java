package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.Body;
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
import soot.jimple.IntConstant;
import soot.jimple.Jimple;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SeedBackwardStaticAnalyzerTest {
    @Before
    public void resetBefore() {
        soot.G.reset();
        System.clearProperty("causynth.protocol.stubs");
        System.clearProperty("causynth.trace.test");
    }

    @After
    public void resetAfter() {
        System.clearProperty("causynth.protocol.stubs");
        System.clearProperty("causynth.trace.test");
        soot.G.reset();
    }

    @Test
    public void nestedReceiverChainReachesParameterCallerAndFieldWriters()
            throws Exception {
        SootClass object = libraryClass("java.lang.Object");
        SootClass runtimeException = libraryClass(
                "java.lang.RuntimeException");
        runtimeException.setSuperclass(object);
        SootMethod runtimeConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        runtimeException.addMethod(runtimeConstructor);

        SootClass failure = applicationClass(
                "example.ReceiverFailure", runtimeException);
        SootMethod failureConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        failure.addMethod(failureConstructor);
        constructorBody(failureConstructor, runtimeConstructor);

        SootClass rootType = applicationClass("example.RootState", object);
        SootClass middleType = applicationClass("example.MiddleState", object);
        SootClass leafType = applicationClass("example.LeafState", object);
        SootField rootMiddle = new SootField("middle",
                RefType.v(middleType.getName()), Modifier.PUBLIC);
        SootField middleLeaf = new SootField("leaf",
                RefType.v(leafType.getName()), Modifier.PUBLIC);
        SootField leafValue = new SootField("value", IntType.v(),
                Modifier.PUBLIC);
        rootType.addField(rootMiddle);
        middleType.addField(middleLeaf);
        leafType.addField(leafValue);

        SootClass owner = applicationClass("example.ReceiverComponent",
                object);
        SootField root = new SootField("root", RefType.v(rootType.getName()),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addField(root);

        SootMethod consume = buildNestedReceiverConsumer(owner, failure,
                failureConstructor, rootType, middleType, leafType,
                rootMiddle, middleLeaf, leafValue);
        SootMethod component = buildNestedReceiverCaller(owner, consume,
                rootType, root);
        SootMethod writeMiddle = buildInstanceFieldWriter(owner,
                "writeMiddle", rootType, middleType, rootMiddle);
        SootMethod writeLeaf = buildInstanceFieldWriter(owner,
                "writeLeaf", middleType, leafType, middleLeaf);
        SootMethod writeValue = buildIntFieldWriter(owner, leafType,
                leafValue);
        ExceptionTargetSite site = new ExceptionTargetSite(
                "receiver-def-use", owner.getName(), consume.getName(),
                "(" + rootType.getName().replace('.', '/') + ")V",
                consume.getSignature(), failure.getName(), 0, -1);
        StaticProgram program = new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, null, site.id, site,
                        "TEST")).analyze();

        assertTrue(program.traceMethods.contains(component.getSignature()));
        assertTrue(program.traceMethods.contains(writeMiddle.getSignature()));
        assertTrue(program.traceMethods.contains(writeLeaf.getSignature()));
        assertTrue(program.traceMethods.contains(writeValue.getSignature()));
        assertTrue(hasEdge(program, "local_def_use",
                consume.getSignature() + "::root",
                consume.getSignature() + "::middle"));
        assertTrue(hasEdge(program, "local_def_use",
                consume.getSignature() + "::middle",
                consume.getSignature() + "::leaf"));
        assertTrue(hasEdge(program, "local_def_use",
                consume.getSignature() + "::leaf",
                consume.getSignature() + "::value"));
        assertTrue(hasEdge(program, "caller_argument",
                component.getSignature() + "::root",
                consume.getSignature() + ".param0:" + rootType.getName()));
        assertTrue(hasEdge(program, "field_read", rootMiddle.getSignature(),
                consume.getSignature() + "::middle"));
        assertTrue(hasEdge(program, "field_read", middleLeaf.getSignature(),
                consume.getSignature() + "::leaf"));
        assertTrue(hasEdge(program, "field_read", leafValue.getSignature(),
                consume.getSignature() + "::value"));
        assertTrue(hasEdge(program, "field_write",
                writeMiddle.getSignature() + "::value",
                rootMiddle.getSignature()));
        assertFalse(hasEdge(program, "field_write",
                writeMiddle.getSignature() + "::receiver",
                rootMiddle.getSignature()));
        assertTrue(hasEdge(program, "field_write",
                writeValue.getSignature() + "::input",
                leafValue.getSignature()));
        assertFalse(hasEdge(program, "field_write",
                writeValue.getSignature() + "::receiver",
                leafValue.getSignature()));
        assertFalse(program.edges.stream().anyMatch(edge ->
                String.valueOf(edge.get("fromCell")).contains("#field:")
                        || String.valueOf(edge.get("toCell"))
                        .contains("#field:")));
    }

    @Test
    public void demandedCollectionMutationIsIndexedLazily() throws Exception {
        SootClass object = libraryClass("java.lang.Object");
        SootClass runtimeException = libraryClass(
                "java.lang.RuntimeException");
        runtimeException.setSuperclass(object);
        SootMethod runtimeConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        runtimeException.addMethod(runtimeConstructor);

        SootClass mapType = libraryClass("java.util.Map");
        mapType.setModifiers(Modifier.PUBLIC | Modifier.INTERFACE);
        SootMethod clear = new SootMethod("clear", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.ABSTRACT);
        mapType.addMethod(clear);

        SootClass failure = applicationClass(
                "example.MutationFailure", runtimeException);
        SootMethod failureConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        failure.addMethod(failureConstructor);
        constructorBody(failureConstructor, runtimeConstructor);

        SootClass state = applicationClass("example.MutationState", object);
        SootField values = new SootField("values",
                RefType.v(mapType.getName()), Modifier.PUBLIC);
        state.addField(values);
        SootClass owner = applicationClass("example.MutationComponent",
                object);
        SootMethod target = buildFieldNullFailure(owner, state, mapType,
                values, failure, failureConstructor);
        SootMethod writer = buildCollectionClear(owner, state, mapType,
                values, clear);

        ExceptionTargetSite site = new ExceptionTargetSite(
                "lazy-mutation", owner.getName(), target.getName(),
                "(" + state.getName().replace('.', '/') + ")V",
                target.getSignature(), failure.getName(), 0, -1);
        StaticProgram program = new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, null, site.id, site,
                        "TEST")).analyze();

        assertTrue(program.traceMethods.contains(writer.getSignature()));
        assertTrue(program.edges.stream().anyMatch(edge ->
                "field_mutation".equals(edge.get("kind"))
                        && values.getSignature().equals(
                        edge.get("toCell"))));
    }

    private static SootMethod buildNestedReceiverConsumer(
            SootClass owner, SootClass failure,
            SootMethod failureConstructor, SootClass rootType,
            SootClass middleType, SootClass leafType,
            SootField rootMiddle, SootField middleLeaf,
            SootField leafValue) {
        SootMethod method = new SootMethod("consumeNested",
                Collections.singletonList(RefType.v(rootType.getName())),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local root = local(body, "root", RefType.v(rootType.getName()));
        Local middle = local(body, "middle",
                RefType.v(middleType.getName()));
        Local leaf = local(body, "leaf", RefType.v(leafType.getName()));
        Local value = local(body, "value", IntType.v());
        Local exception = local(body, "failure", RefType.v(failure.getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(root,
                Jimple.v().newParameterRef((RefType) root.getType(), 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(middle,
                Jimple.v().newInstanceFieldRef(root, rootMiddle.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(leaf,
                Jimple.v().newInstanceFieldRef(middle, middleLeaf.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newInstanceFieldRef(leaf, leafValue.makeRef())));
        Unit normalReturn = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(value, IntConstant.v(0)), normalReturn));
        body.getUnits().add(Jimple.v().newAssignStmt(exception,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(exception,
                        failureConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(exception));
        body.getUnits().add(normalReturn);
        return method;
    }

    private static SootMethod buildNestedReceiverCaller(
            SootClass owner, SootMethod consume, SootClass rootType,
            SootField rootField) {
        SootMethod method = new SootMethod("componentEntry",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local root = local(body, "root", RefType.v(rootType.getName()));
        body.getUnits().add(Jimple.v().newAssignStmt(root,
                Jimple.v().newStaticFieldRef(rootField.makeRef())));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(consume.makeRef(), root)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static SootMethod buildFieldNullFailure(
            SootClass owner, SootClass stateType, SootClass mapType,
            SootField values, SootClass failure,
            SootMethod failureConstructor) {
        SootMethod method = new SootMethod("failWhenValuesMissing",
                Collections.singletonList(RefType.v(stateType.getName())),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local state = local(body, "state", RefType.v(stateType.getName()));
        Local map = local(body, "map", RefType.v(mapType.getName()));
        Local exception = local(body, "failure",
                RefType.v(failure.getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(state,
                Jimple.v().newParameterRef((RefType) state.getType(), 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(map,
                Jimple.v().newInstanceFieldRef(state, values.makeRef())));
        Unit normalReturn = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(map, soot.jimple.NullConstant.v()),
                normalReturn));
        body.getUnits().add(Jimple.v().newAssignStmt(exception,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(exception,
                        failureConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(exception));
        body.getUnits().add(normalReturn);
        return method;
    }

    private static SootMethod buildCollectionClear(
            SootClass owner, SootClass stateType, SootClass mapType,
            SootField values, SootMethod clear) {
        SootMethod method = new SootMethod("clearValues",
                Collections.singletonList(RefType.v(stateType.getName())),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local state = local(body, "state", RefType.v(stateType.getName()));
        Local map = local(body, "map", RefType.v(mapType.getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(state,
                Jimple.v().newParameterRef((RefType) state.getType(), 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(map,
                Jimple.v().newInstanceFieldRef(state, values.makeRef())));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(map, clear.makeRef())));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static SootMethod buildInstanceFieldWriter(
            SootClass owner, String name, SootClass receiverType,
            SootClass valueType, SootField field) {
        SootMethod method = new SootMethod(name,
                Arrays.asList(RefType.v(receiverType.getName()),
                        RefType.v(valueType.getName())),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = local(body, "receiver",
                RefType.v(receiverType.getName()));
        Local value = local(body, "value", RefType.v(valueType.getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newParameterRef((RefType) receiver.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef((RefType) value.getType(), 1)));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef()),
                value));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static SootMethod buildIntFieldWriter(
            SootClass owner, SootClass receiverType, SootField field) {
        SootMethod method = new SootMethod("writeValue",
                Arrays.asList(RefType.v(receiverType.getName()), IntType.v()),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = local(body, "receiver",
                RefType.v(receiverType.getName()));
        Local value = local(body, "input", IntType.v());
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newParameterRef((RefType) receiver.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef(IntType.v(), 1)));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef()),
                value));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static boolean hasEdge(StaticProgram program, String kind,
                                   String from, String to) {
        return program.edges.stream().anyMatch(edge ->
                kind.equals(edge.get("kind"))
                        && from.equals(edge.get("fromCell"))
                        && to.equals(edge.get("toCell")));
    }

    private static void constructorBody(SootMethod constructor,
                                        SootMethod parentConstructor) {
        Body body = Jimple.v().newBody(constructor);
        constructor.setActiveBody(body);
        Local receiver = local(body, "this",
                RefType.v(constructor.getDeclaringClass().getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef((RefType) receiver.getType())));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(receiver,
                        parentConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
    }

    private static SootClass applicationClass(String name, SootClass parent) {
        SootClass sootClass = new SootClass(name, Modifier.PUBLIC);
        sootClass.setSuperclass(parent);
        Scene.v().addClass(sootClass);
        sootClass.setApplicationClass();
        return sootClass;
    }

    private static SootClass libraryClass(String name) {
        SootClass sootClass = new SootClass(name, Modifier.PUBLIC);
        Scene.v().addClass(sootClass);
        sootClass.setLibraryClass();
        return sootClass;
    }

    private static Local local(Body body, String name, soot.Type type) {
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }

}
