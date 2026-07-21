package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.Unit;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.TableSwitchStmt;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class CausynthBranchShapeTest {
    @Test
    public void binarySuccessorsAreFallThroughThenTaken() {
        Body body = Jimple.v().newBody();
        Unit taken = Jimple.v().newNopStmt();
        IfStmt branch = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(IntConstant.v(1), IntConstant.v(0)),
                taken);
        Unit fallThrough = Jimple.v().newNopStmt();
        body.getUnits().add(branch);
        body.getUnits().add(fallThrough);
        body.getUnits().add(taken);

        CausynthBranchShape shape = CausynthBranchShape.from(body, branch);
        assertEquals(CausynthBranchShape.IF, shape.kind);
        assertEquals(2, shape.successorCount());
        assertSame(fallThrough, shape.successors.get(0));
        assertSame(taken, shape.successors.get(1));
    }

    @Test
    public void tableSwitchRetainsCaseEdgeIdentityWhenTargetsAlias() {
        Body body = Jimple.v().newBody();
        Local key = Jimple.v().newLocal("key", IntType.v());
        Unit shared = Jimple.v().newNopStmt();
        Unit third = Jimple.v().newNopStmt();
        Unit defaultTarget = Jimple.v().newNopStmt();
        TableSwitchStmt branch = Jimple.v().newTableSwitchStmt(key, 4, 6,
                Arrays.asList(shared, shared, third), defaultTarget);
        body.getUnits().add(branch);
        body.getUnits().add(shared);
        body.getUnits().add(third);
        body.getUnits().add(defaultTarget);

        CausynthBranchShape shape = CausynthBranchShape.from(body, branch);
        assertEquals(CausynthBranchShape.TABLE_SWITCH, shape.kind);
        assertEquals(Arrays.asList(4, 5, 6), shape.caseKeys);
        assertEquals(3, shape.defaultSuccessorIndex);
        assertEquals(4, shape.successorCount());
        assertSame(shape.successors.get(0), shape.successors.get(1));

        Map<String, Object> metadata = new LinkedHashMap<>();
        shape.annotate(metadata);
        assertEquals("STATIC_BRANCH_CASE_ORDER_THEN_DEFAULT_V1",
                metadata.get("successorIndexAuthority"));
        assertEquals(Arrays.asList(4, 5, 6),
                metadata.get("switchCaseKeys"));
    }

    @Test
    public void lookupSwitchPreservesClassfilePairOrderThenDefault() {
        Body body = Jimple.v().newBody();
        Local key = Jimple.v().newLocal("key", IntType.v());
        Unit first = Jimple.v().newNopStmt();
        Unit second = Jimple.v().newNopStmt();
        Unit third = Jimple.v().newNopStmt();
        Unit defaultTarget = Jimple.v().newNopStmt();
        LookupSwitchStmt branch = Jimple.v().newLookupSwitchStmt(key,
                Arrays.asList(IntConstant.v(-100), IntConstant.v(7),
                        IntConstant.v(1000)),
                Arrays.asList(first, second, third), defaultTarget);
        body.getUnits().add(branch);
        body.getUnits().add(first);
        body.getUnits().add(second);
        body.getUnits().add(third);
        body.getUnits().add(defaultTarget);

        CausynthBranchShape shape = CausynthBranchShape.from(body, branch);
        assertEquals(CausynthBranchShape.LOOKUP_SWITCH, shape.kind);
        assertEquals(Arrays.asList(-100, 7, 1000), shape.caseKeys);
        assertEquals("-100,7,1000", shape.encodedCaseKeys());
        assertTrue(shape.isSwitch());
        assertSame(defaultTarget, shape.successors.get(3));
    }
}
