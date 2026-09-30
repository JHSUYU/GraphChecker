package edu.uva.liftlab.graphchecker.causynth;

import soot.Local;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.ThisRef;

import java.util.List;
import java.util.function.Predicate;

/**
 * Whether a library call's result depends on its receiver's state
 * (SYMBOL-SCOPE §2.2): {@code chm.get(k)} past the container contracts,
 * {@code navMap.floorKey(k)}, {@code conf.getBoolean(key, d)} on a field's
 * object.  The slice otherwise drops a library call's receiver, so the state
 * behind it never enters {@code S}.
 *
 * <p>It does when the callee's owner is no identity, reflection or logging
 * type ({@link #stateful}) and the receiver is shared state: its definition,
 * through copies and casts, is {@code this}, a field read, or a structural
 * accessor's result.  A receiver the method allocated, or a parameter, is
 * the method's own object, not state another occurrence stores.  The caller
 * has already ruled out application calls, container contracts, value types
 * and accessors, which state their dependence themselves.</p>
 */
final class LibraryReceivers {
    /** Packages whose objects hold no state a guard decides on. */
    private static final String[] STATELESS = {
        "org.slf4j.", "org.apache.log4j.", "org.apache.logging.",
        "org.apache.commons.logging.", "java.util.logging.",
    };

    private LibraryReceivers() {
    }

    /** Whether a call on {@code owner} reads its receiver's state. */
    static boolean stateful(String owner, String name) {
        if ("java.lang.Object".equals(owner)
                || "java.lang.Class".equals(owner)
                || "getClass".equals(name) || "hashCode".equals(name)
                || "toString".equals(name)) {
            return false;
        }
        for (String prefix : STATELESS) {
            if (owner.startsWith(prefix)) return false;
        }
        for (String segment : owner.split("\\.")) {
            if ("metrics".equals(segment) || "metrics2".equals(segment)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether the receiver {@code local} of the call at {@code index} holds
     * shared state: its last definition before the call, through copies and
     * casts, reads {@code this}, a field, or an {@code accessor}'s result.
     */
    static boolean shared(List<Unit> units, int index, Local local,
                          Predicate<InvokeExpr> accessor) {
        Local wanted = local;
        for (int at = index - 1; at >= 0; at--) {
            Unit unit = units.get(at);
            if (unit instanceof IdentityStmt
                    && ((IdentityStmt) unit).getLeftOp() == wanted) {
                return ((IdentityStmt) unit).getRightOp() instanceof ThisRef;
            }
            if (!(unit instanceof AssignStmt)
                    || ((AssignStmt) unit).getLeftOp() != wanted) {
                continue;
            }
            Value right = ((AssignStmt) unit).getRightOp();
            if (right instanceof CastExpr) right = ((CastExpr) right).getOp();
            if (right instanceof Local) {
                wanted = (Local) right;
                continue;
            }
            return right instanceof FieldRef
                    || right instanceof InvokeExpr
                    && accessor.test((InvokeExpr) right);
        }
        return false;
    }
}
