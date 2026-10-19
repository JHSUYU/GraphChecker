package edu.uva.liftlab.graphchecker.causynth;

import soot.Local;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.StaticInvokeExpr;

import java.util.LinkedHashSet;
import java.util.Set;

final class CreatedFrom {
    private CreatedFrom() {
    }

    static Set<SootClass> classes(Iterable<Unit> units, Local local) {
        Set<SootClass> classes = new LinkedHashSet<SootClass>();
        for (Unit unit : units) {
            if (!(unit instanceof AssignStmt)
                    || ((AssignStmt) unit).getLeftOp() != local) {
                continue;
            }
            Value created = ((AssignStmt) unit).getRightOp();
            SootClass type = created instanceof NewExpr
                    ? ((NewExpr) created).getBaseType().getSootClass()
                    : created instanceof StaticInvokeExpr
                    ? ((InvokeExpr) created).getMethodRef()
                    .getDeclaringClass() : null;
            if (type != null && type.isApplicationClass()) classes.add(type);
        }
        return classes;
    }

    static SootMethod implementation(SootClass type, String subSignature) {
        for (SootClass owner = type; owner != null
                && owner.resolvingLevel() >= SootClass.SIGNATURES;
             owner = owner.hasSuperclass() ? owner.getSuperclass() : null) {
            SootMethod method = owner.getMethodUnsafe(subSignature);
            if (method != null && method.isConcrete()) return method;
        }
        return null;
    }
}
