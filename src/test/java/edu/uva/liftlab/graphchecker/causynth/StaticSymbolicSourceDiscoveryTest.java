package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.Body;
import soot.BooleanType;
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
            "RPC_COMPARE.VALUE", "RPC_COMPARE.ADJUSTMENT",
            "RPC_COMPARE.GUARD_LEFT", "RPC_COMPARE.GUARD_RIGHT",
            "RPC_COMPARE.LOWER_BOUND", "RPC_COMPARE.UPPER_BOUND",
            "RPC_COMPARE.BIAS", "RPC_COMPARE.PIVOT");

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
    public void sharedHelperDeclaresEightSourcesForBothRpcRegions()
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
            assertEquals(8, declarations.size());
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

    @Test(expected = java.io.IOException.class)
    public void rejectsHookWhoseOwnerIsNotThis() throws Exception {
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
        SootClass node = new SootClass("example.BadNode", Modifier.PUBLIC);
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
                        StringConstant.v("RPC_COMPARE.VALUE"), other,
                        StringConstant.v(field.getSignature()))));
        body.getUnits().add(Jimple.v().newReturnStmt(
                soot.jimple.LongConstant.v(0L)));
        StaticProgram program = new StaticProgram();
        program.regions.add(region("REGION.BAD", rpc));
        StaticSymbolicSourceDiscovery.discover(program);
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
