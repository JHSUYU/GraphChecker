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

/**
 * The class an object a local holds was created from, read off the
 * method's own assignments of it: a {@code new C}, or a static method of an
 * application class C -- the {@code bootstrap$} factory of Soot's desugared
 * lambda or method reference ({@code X$lambda_m_N__k}).  One rule for the
 * slice entering a functional argument's methods ({@code
 * SeedBackwardStaticAnalyzer#enterFunctionalArguments}) and for a guard on
 * a call's return reaching the method that call runs ({@code
 * BooleanReturns}): a local read from a field or a parameter states no
 * class.
 */
final class CreatedFrom {
    private CreatedFrom() {
    }

    /** The application classes {@code local}'s definitions among {@code
     *  units} create its object of. */
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
            // Only the analysed scope's classes have a method to enter.
            if (type != null && type.isApplicationClass()) classes.add(type);
        }
        return classes;
    }

    /** The concrete method a class runs for one subsignature: its own or
     *  its nearest superclass's; null when none states one. */
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
