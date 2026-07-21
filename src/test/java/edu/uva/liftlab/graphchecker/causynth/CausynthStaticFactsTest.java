package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;
import soot.IntType;
import soot.Local;
import soot.Unit;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CausynthStaticFactsTest {
    @Test
    public void parsesOnlyTopLevelRenderedInvocationArguments() {
        assertEquals(Arrays.asList("first", "nested(left, right)",
                        "java.util.Map<java.lang.String,java.lang.Integer>",
                        "values[index, other]"),
                CausynthStaticFacts.splitTopLevelArgs(
                        "first, nested(left, right), "
                                + "java.util.Map<java.lang.String,"
                                + "java.lang.Integer>, values[index, other]"));
        assertEquals(Arrays.asList("$r1", "7"),
                CausynthStaticFacts.actualInvokeArgs(
                        "virtualinvoke $r0.<example.Target: void "
                                + "call(java.lang.Object,int)>($r1, 7)"));
        assertTrue(CausynthStaticFacts.actualInvokeArgs(
                "return $i0").isEmpty());
    }

    @Test
    public void decodesIfAndSwitchUnitsAsBranchFacts() {
        Unit target = Jimple.v().newNopStmt();
        Unit conditional = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(IntConstant.v(1), IntConstant.v(0)),
                target);
        CausynthStaticFacts.Fact ifFact = new CausynthStaticFacts.Fact(
                "<example.Target: void run()>", 3, conditional);
        assertTrue(ifFact.isBranch);
        assertFalse(ifFact.isReturn);
        assertEquals(3, ifFact.unitIndex);

        Local key = Jimple.v().newLocal("key", IntType.v());
        Unit tableSwitch = Jimple.v().newTableSwitchStmt(key, 0, 1,
                Arrays.asList(Jimple.v().newNopStmt(),
                        Jimple.v().newNopStmt()), target);
        CausynthStaticFacts.Fact switchFact =
                new CausynthStaticFacts.Fact(
                        "<example.Target: void run()>", 4, tableSwitch);
        assertTrue(switchFact.isBranch);
        assertEquals(Collections.singletonList("key"), switchFact.uses);
    }

    @Test
    public void extractsOnlyTheDeclaredFieldOwner() {
        assertEquals("example.Payload", CausynthStaticFacts.fieldOwner(
                "<example.Payload: long deadline>"));
        assertEquals("", CausynthStaticFacts.fieldOwner("deadline"));
        assertEquals("", CausynthStaticFacts.fieldOwner(null));
    }
}
