package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
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
import soot.VoidType;
import soot.jimple.Jimple;
import soot.jimple.IntConstant;
import soot.jimple.NullConstant;
import soot.jimple.StringConstant;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class StaticSymbolicSourceDiscoveryTest {
    private static final List<String> SOURCE_IDS = Arrays.asList(
            "RPC_COMPARE.A", "RPC_COMPARE.B", "RPC_COMPARE.C",
            "RPC_COMPARE.D", "RPC_COMPARE.E");

    @Before
    public void resetBefore() {
        soot.G.reset();
    }

    @After
    public void resetAfter() {
        soot.G.reset();
    }

    @Test
    @SuppressWarnings("unchecked")
    public void sharedHelperDeclaresFiveSourcesForBothRpcRegions()
            throws Exception {
        SootClass hook = new SootClass(
                "example.CausynthSymbolicSource", Modifier.PUBLIC);
        hook.setLibraryClass();
        Scene.v().addClass(hook);
        SootMethod symbolize = new SootMethod("symbolize", Arrays.asList(
                RefType.v("java.lang.String"),
                RefType.v("java.lang.Object"),
                RefType.v("java.lang.String")), BooleanType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        hook.addMethod(symbolize);

        SootClass node = new SootClass("example.DataNode", Modifier.PUBLIC);
        Scene.v().addClass(node);
        node.setApplicationClass();
        List<SootField> fields = new ArrayList<>();
        for (int index = 0; index < SOURCE_IDS.size(); index++) {
            SootField field = new SootField("value" + index,
                    LongType.v(), Modifier.PRIVATE);
            node.addField(field);
            fields.add(field);
        }
        SootMethod helper = helper(node, symbolize, fields);
        SootMethod rpcA = rpc(node, helper, fields.get(0),
                "getCausynthValueA");
        SootMethod rpcB = rpc(node, helper, fields.get(1),
                "getCausynthValueB");
        assertTrue(node.isApplicationClass());
        assertTrue(rpcA.isConcrete());
        assertEquals(rpcA, Scene.v().getMethod(rpcA.getSignature()));

        StaticProgram program = new StaticProgram();
        program.regions.add(region("REGION.A", rpcA));
        program.regions.add(region("REGION.B", rpcB));

        StaticSymbolicSourceDiscovery.discover(program);

        for (Map<String, Object> region : program.regions) {
            List<Map<String, Object>> declarations =
                    (List<Map<String, Object>>) region.get(
                            StaticSymbolicSourceDeclaration.FIELD);
            assertEquals(5, declarations.size());
            for (int index = 0; index < declarations.size(); index++) {
                Map<String, Object> declaration = declarations.get(index);
                assertEquals(SOURCE_IDS.get(index),
                        declaration.get("sourceId"));
                assertEquals(fields.get(index).getSignature(),
                        declaration.get("fieldSignature"));
                assertEquals(helper.getSignature(),
                        declaration.get("declarationMethod"));
                assertEquals(StaticSymbolicSourceDeclaration.AUTHORITY,
                        declaration.get("authority"));
            }
        }
    }

    @Test
    @SuppressWarnings("unchecked")
    public void acceptsExactNonThisOwnerSelectedByTheHook() throws Exception {
        SootClass hook = new SootClass(
                "example.CausynthSymbolicSource", Modifier.PUBLIC);
        hook.setLibraryClass();
        Scene.v().addClass(hook);
        SootMethod symbolize = new SootMethod("symbolize", Arrays.asList(
                RefType.v("java.lang.String"),
                RefType.v("java.lang.Object"),
                RefType.v("java.lang.String")), BooleanType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        hook.addMethod(symbolize);
        SootClass node = new SootClass("example.SelectedOwnerNode",
                Modifier.PUBLIC);
        Scene.v().addClass(node);
        node.setApplicationClass();
        SootField field = new SootField("value", LongType.v());
        node.addField(field);
        SootMethod rpc = new SootMethod("get", Collections.emptyList(),
                LongType.v(), Modifier.PUBLIC);
        node.addMethod(rpc);
        Body body = Jimple.v().newBody(rpc);
        rpc.setActiveBody(body);
        Local self = thisLocal(body, node, "self");
        Local other = Jimple.v().newLocal("other", RefType.v(node.getName()));
        body.getLocals().add(other);
        body.getUnits().add(Jimple.v().newAssignStmt(other, self));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(symbolize.makeRef(),
                        StringConstant.v("RPC_COMPARE.A"), other,
                        StringConstant.v(field.getSignature()))));
        body.getUnits().add(Jimple.v().newReturnStmt(
                soot.jimple.LongConstant.v(0L)));
        StaticProgram program = new StaticProgram();
        program.regions.add(region("REGION.SELECTED_OWNER", rpc));
        StaticSymbolicSourceDiscovery.discover(program);
        List<Map<String, Object>> declarations =
                (List<Map<String, Object>>) program.regions.get(0).get(
                        StaticSymbolicSourceDeclaration.FIELD);
        assertEquals(1, declarations.size());
        assertEquals("RPC_COMPARE.A",
                declarations.get(0).get("sourceId"));
        assertEquals(field.getSignature(),
                declarations.get(0).get("fieldSignature"));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void discoversExactFieldOnObjectSelectedFromArrayZero()
            throws Exception {
        SootClass hook = new SootClass(
                "example.CausynthSymbolicSource", Modifier.PUBLIC);
        hook.setLibraryClass();
        Scene.v().addClass(hook);
        SootMethod symbolize = new SootMethod("symbolize", Arrays.asList(
                RefType.v("java.lang.String"),
                RefType.v("java.lang.Object"),
                RefType.v("java.lang.String")), BooleanType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        hook.addMethod(symbolize);

        SootClass element = new SootClass("example.Element", Modifier.PUBLIC);
        Scene.v().addClass(element);
        element.setApplicationClass();
        SootField value = new SootField("value", LongType.v());
        element.addField(value);

        SootClass node = new SootClass("example.ArrayOwnerNode",
                Modifier.PUBLIC);
        Scene.v().addClass(node);
        node.setApplicationClass();
        ArrayType elementsType = ArrayType.v(RefType.v(element.getName()), 1);
        SootMethod rpc = new SootMethod("getFromArray",
                Collections.singletonList(elementsType), LongType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        node.addMethod(rpc);
        Body body = Jimple.v().newBody(rpc);
        rpc.setActiveBody(body);
        Local elements = Jimple.v().newLocal("elements", elementsType);
        Local selected = Jimple.v().newLocal("selected",
                RefType.v(element.getName()));
        body.getLocals().add(elements);
        body.getLocals().add(selected);
        body.getUnits().add(Jimple.v().newIdentityStmt(elements,
                Jimple.v().newParameterRef(elementsType, 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(selected,
                Jimple.v().newArrayRef(elements, IntConstant.v(0))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(symbolize.makeRef(),
                        StringConstant.v("ARRAY.ELEMENT.ZERO"), selected,
                        StringConstant.v(value.getSignature()))));
        body.getUnits().add(Jimple.v().newReturnStmt(
                soot.jimple.LongConstant.v(0L)));

        StaticProgram program = new StaticProgram();
        program.regions.add(region("REGION.ARRAY.ELEMENT.ZERO", rpc));
        StaticSymbolicSourceDiscovery.discover(program);

        List<Map<String, Object>> declarations =
                (List<Map<String, Object>>) program.regions.get(0).get(
                        StaticSymbolicSourceDeclaration.FIELD);
        assertEquals(1, declarations.size());
        Map<String, Object> declaration = declarations.get(0);
        assertEquals("ARRAY.ELEMENT.ZERO", declaration.get("sourceId"));
        assertEquals(value.getSignature(), declaration.get("fieldSignature"));
        assertEquals(rpc.getSignature(), declaration.get("declarationMethod"));
        assertEquals(2, ((Number) declaration.get(
                "declarationUnitIndex")).intValue());
    }

    @Test(expected = java.io.IOException.class)
    public void rejectsNullOwnerInsteadOfInventingAnObject() throws Exception {
        SootClass hook = new SootClass(
                "example.CausynthSymbolicSource", Modifier.PUBLIC);
        hook.setLibraryClass();
        Scene.v().addClass(hook);
        SootMethod symbolize = new SootMethod("symbolize", Arrays.asList(
                RefType.v("java.lang.String"),
                RefType.v("java.lang.Object"),
                RefType.v("java.lang.String")), BooleanType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        hook.addMethod(symbolize);
        SootClass node = new SootClass("example.NullOwnerNode",
                Modifier.PUBLIC);
        Scene.v().addClass(node);
        node.setApplicationClass();
        SootField value = new SootField("value", LongType.v());
        node.addField(value);
        SootMethod rpc = new SootMethod("get", Collections.emptyList(),
                LongType.v(), Modifier.PUBLIC | Modifier.STATIC);
        node.addMethod(rpc);
        Body body = Jimple.v().newBody(rpc);
        rpc.setActiveBody(body);
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(symbolize.makeRef(),
                        StringConstant.v("NULL.OWNER"), NullConstant.v(),
                        StringConstant.v(value.getSignature()))));
        body.getUnits().add(Jimple.v().newReturnStmt(
                soot.jimple.LongConstant.v(0L)));
        StaticProgram program = new StaticProgram();
        program.regions.add(region("REGION.NULL.OWNER", rpc));

        StaticSymbolicSourceDiscovery.discover(program);
    }

    @Test(expected = java.io.IOException.class)
    public void rejectsSameSourceAtTwoDifferentHookSites() throws Exception {
        SootClass hook = new SootClass(
                "example.CausynthSymbolicSource", Modifier.PUBLIC);
        hook.setLibraryClass();
        Scene.v().addClass(hook);
        SootMethod symbolize = new SootMethod("symbolize", Arrays.asList(
                RefType.v("java.lang.String"),
                RefType.v("java.lang.Object"),
                RefType.v("java.lang.String")), BooleanType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        hook.addMethod(symbolize);
        SootClass node = new SootClass("example.DuplicateNode",
                Modifier.PUBLIC);
        Scene.v().addClass(node);
        node.setApplicationClass();
        SootField field = new SootField("value", LongType.v());
        node.addField(field);
        SootMethod rpc = new SootMethod("get", Collections.emptyList(),
                LongType.v(), Modifier.PUBLIC);
        node.addMethod(rpc);
        Body body = Jimple.v().newBody(rpc);
        rpc.setActiveBody(body);
        Local self = thisLocal(body, node, "self");
        for (int index = 0; index < 2; index++) {
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(symbolize.makeRef(),
                            StringConstant.v("DUPLICATE"), self,
                            StringConstant.v(field.getSignature()))));
        }
        body.getUnits().add(Jimple.v().newReturnStmt(
                soot.jimple.LongConstant.v(0L)));
        StaticProgram program = new StaticProgram();
        program.regions.add(region("REGION.DUPLICATE", rpc));
        StaticSymbolicSourceDiscovery.discover(program);
    }

    @Test
    @SuppressWarnings("unchecked")
    public void discoversOrderedPublishConsumeSitesAndRichTraceMethods()
            throws Exception {
        SootClass hook = new SootClass(
                "example.CausynthSymbolicSource", Modifier.PUBLIC);
        hook.setLibraryClass();
        Scene.v().addClass(hook);
        SootMethod symbolize = new SootMethod("symbolize", Arrays.asList(
                RefType.v("java.lang.String"),
                RefType.v("java.lang.Object"),
                RefType.v("java.lang.String")), BooleanType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        SootMethod selected = new SootMethod("selectedIntValue",
                Collections.singletonList(RefType.v("java.lang.String")),
                RefType.v("java.lang.Integer"),
                Modifier.PUBLIC | Modifier.STATIC);
        hook.addMethod(symbolize);
        hook.addMethod(selected);

        SootClass node = new SootClass("example.PhasedNode", Modifier.PUBLIC);
        Scene.v().addClass(node);
        node.setApplicationClass();
        SootField keyId = new SootField("keyId", IntType.v());
        node.addField(keyId);

        SootMethod phaseHelper = new SootMethod("rotate",
                Collections.emptyList(), VoidType.v(), Modifier.PRIVATE);
        node.addMethod(phaseHelper);
        Body helperBody = Jimple.v().newBody(phaseHelper);
        phaseHelper.setActiveBody(helperBody);
        Local helperThis = thisLocal(helperBody, node, "phaseThis");
        Local selectedValue = Jimple.v().newLocal("selected",
                RefType.v("java.lang.Integer"));
        helperBody.getLocals().add(selectedValue);
        helperBody.getUnits().add(Jimple.v().newAssignStmt(selectedValue,
                Jimple.v().newStaticInvokeExpr(selected.makeRef(),
                        StringConstant.v("ROTATING.KEY"))));
        helperBody.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(symbolize.makeRef(),
                        StringConstant.v("ROTATING.KEY"), helperThis,
                        StringConstant.v(keyId.getSignature()))));
        helperBody.getUnits().add(Jimple.v().newReturnVoidStmt());

        SootMethod root = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC);
        node.addMethod(root);
        Body rootBody = Jimple.v().newBody(root);
        root.setActiveBody(rootBody);
        Local rootThis = thisLocal(rootBody, node, "rootThis");
        rootBody.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newVirtualInvokeExpr(rootThis,
                        phaseHelper.makeRef())));
        rootBody.getUnits().add(Jimple.v().newReturnVoidStmt());

        StaticProgram program = new StaticProgram();
        program.traceMethods.add(root.getSignature());
        Map<String, Object> region = region("REGION.PHASED", root);
        program.regions.add(region);

        StaticSymbolicSourceDiscovery.discover(program);

        List<Map<String, Object>> phases =
                (List<Map<String, Object>>) region.get(
                        ConfiguredSourcePhaseContract.DECLARATION_FIELD);
        assertEquals(2, phases.size());
        assertEquals("CONSUME", phases.get(0).get("phase"));
        assertEquals("PUBLISH", phases.get(1).get("phase"));
        for (Map<String, Object> phase : phases) {
            assertEquals("ROTATING.KEY", phase.get("sourceId"));
            assertEquals(keyId.getSignature(),
                    phase.get("fieldSignature"));
            assertEquals(phaseHelper.getSignature(),
                    phase.get("declarationMethod"));
        }
        assertEquals(Collections.singletonList(phaseHelper.getSignature()),
                region.get(ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD));
        assertTrue(program.traceMethods.contains(root.getSignature()));
        assertTrue(program.traceMethods.contains(phaseHelper.getSignature()));
    }

    private static SootMethod helper(
            SootClass node, SootMethod symbolize, List<SootField> fields) {
        SootMethod helper = new SootMethod("symbolizeInputs",
                Collections.emptyList(), VoidType.v(), Modifier.PRIVATE);
        node.addMethod(helper);
        Body body = Jimple.v().newBody(helper);
        helper.setActiveBody(body);
        Local self = thisLocal(body, node, "helperThis");
        for (int index = 0; index < fields.size(); index++) {
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(symbolize.makeRef(),
                            StringConstant.v(SOURCE_IDS.get(index)), self,
                            StringConstant.v(
                                    fields.get(index).getSignature()))));
        }
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return helper;
    }

    private static SootMethod rpc(
            SootClass node, SootMethod helper, SootField output,
            String name) {
        SootMethod rpc = new SootMethod(name, Collections.emptyList(),
                LongType.v(), Modifier.PUBLIC);
        node.addMethod(rpc);
        Body body = Jimple.v().newBody(rpc);
        rpc.setActiveBody(body);
        Local self = thisLocal(body, node, name + "This");
        Local result = Jimple.v().newLocal("result", LongType.v());
        body.getLocals().add(result);
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newVirtualInvokeExpr(self, helper.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(result,
                Jimple.v().newInstanceFieldRef(self, output.makeRef())));
        body.getUnits().add(Jimple.v().newReturnStmt(result));
        return rpc;
    }

    private static Local thisLocal(
            Body body, SootClass owner, String name) {
        Local self = Jimple.v().newLocal(name, RefType.v(owner.getName()));
        body.getLocals().add(self);
        body.getUnits().add(Jimple.v().newIdentityStmt(self,
                Jimple.v().newThisRef(RefType.v(owner.getName()))));
        return self;
    }

    private static Map<String, Object> region(
            String id, SootMethod method) {
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("schemaVersion", 3);
        region.put("kind", "REGION_SKELETON");
        region.put("regionId", id);
        region.put("rootMethod", method.getSignature());
        region.put("anchorMethod", method.getSignature());
        region.put("methods", Collections.singletonList(
                method.getSignature()));
        return region;
    }
}
