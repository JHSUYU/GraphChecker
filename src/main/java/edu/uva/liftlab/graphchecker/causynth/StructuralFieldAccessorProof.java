package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ThisRef;

import java.util.LinkedHashSet;
import java.util.Set;

/** Static proof that a no-argument getter is one exact field read. */
final class StructuralFieldAccessorProof {
    private StructuralFieldAccessorProof() {
    }

    /**
     * A JDK atomic's {@code get()}: the value field it reads, off {@link
     * SharedFieldFlow#atomicRead}'s table rather than a body, which a JDK
     * class need not have loaded -- {@code AtomicReference.get()} is its
     * {@code value}, {@code AtomicBoolean.get()} its {@code value != 0}.
     * Null for any other call, or when the field does not resolve.
     */
    static SootField atomicField(String accessor) {
        String field = SharedFieldFlow.atomicRead(accessor);
        return field.isEmpty() ? null : Scene.v().grabField(field);
    }

    static SootField exactField(SootMethod method) {
        if (method == null || method.isStatic() || method.isNative()
                || method.isSynchronized() || !method.isConcrete()
                || method.getParameterCount() != 0) {
            return null;
        }
        Body body = CausynthStaticFacts.activeBody(method);
        if (body == null || !body.getTraps().isEmpty()) return null;

        Set<Local> receiverAliases = new LinkedHashSet<>();
        Set<Local> valueAliases = new LinkedHashSet<>();
        SootField field = null;
        boolean receiverIdentitySeen = false;
        boolean returnSeen = false;
        for (Unit unit : body.getUnits()) {
            if (unit instanceof IdentityStmt) {
                IdentityStmt identity = (IdentityStmt) unit;
                if (receiverIdentitySeen
                        || !(identity.getLeftOp() instanceof Local)
                        || !(identity.getRightOp() instanceof ThisRef)) {
                    return null;
                }
                receiverAliases.add((Local) identity.getLeftOp());
                receiverIdentitySeen = true;
                continue;
            }
            if (unit instanceof AssignStmt) {
                AssignStmt assignment = (AssignStmt) unit;
                if (!(assignment.getLeftOp() instanceof Local)) return null;
                Local target = (Local) assignment.getLeftOp();
                Value source = assignment.getRightOp();
                boolean receiverAlias = aliasOf(source, receiverAliases);
                boolean valueAlias = aliasOf(source, valueAliases);
                receiverAliases.remove(target);
                valueAliases.remove(target);
                if (receiverAlias) {
                    receiverAliases.add(target);
                    continue;
                }
                if (valueAlias) {
                    valueAliases.add(target);
                    continue;
                }
                if (!(source instanceof InstanceFieldRef) || field != null) {
                    return null;
                }
                InstanceFieldRef read = (InstanceFieldRef) source;
                if (!(read.getBase() instanceof Local)
                        || !receiverAliases.contains((Local) read.getBase())) {
                    return null;
                }
                try {
                    field = read.getField();
                } catch (RuntimeException unresolved) {
                    return null;
                }
                if (field == null || field.isStatic()) return null;
                valueAliases.add(target);
                continue;
            }
            if (unit instanceof ReturnStmt) {
                Value returned = ((ReturnStmt) unit).getOp();
                if (returnSeen || !(returned instanceof Local)
                        || !valueAliases.contains((Local) returned)) {
                    return null;
                }
                returnSeen = true;
                continue;
            }
            return null;
        }
        if (!receiverIdentitySeen || !returnSeen || field == null
                || !field.getType().equals(method.getReturnType())) {
            return null;
        }
        return field;
    }

    /** True when {@code source}, through any cast, is one of the aliases. */
    private static boolean aliasOf(Value source, Set<Local> aliases) {
        Value operand = source instanceof CastExpr
                ? ((CastExpr) source).getOp() : source;
        return operand instanceof Local && aliases.contains((Local) operand);
    }
}
