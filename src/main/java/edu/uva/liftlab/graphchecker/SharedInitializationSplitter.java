package edu.uva.liftlab.graphchecker;

import soot.Body;
import soot.BodyTransformer;
import soot.G;
import soot.Local;
import soot.Pack;
import soot.PackManager;
import soot.Scene;
import soot.Transform;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.dexpler.DexNullArrayRefTransformer;
import soot.dexpler.DexNullThrowTransformer;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.Jimple;
import soot.jimple.toolkits.scalar.ConstantPropagatorAndFolder;
import soot.jimple.toolkits.scalar.CopyPropagator;
import soot.jimple.toolkits.scalar.DeadAssignmentEliminator;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraphFactory;
import soot.toolkits.scalar.FlowSensitiveConstantPropagator;
import soot.toolkits.scalar.LocalDefs;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Soot's {@code jb.sils} ({@code SharedInitializationLocalSplitter}), with
 * its choices taken in body order.
 *
 * <p>The phase gives each use of a local that only constants define its own
 * copy of the local, assigned right after each of those constants, so the
 * typing can give the uses different types.  Soot keeps a local's uses in a
 * hash set of objects it has just made, so which copy a use got, and in
 * which order the copies' assignments followed the constant, followed
 * identity hashes: two runs of one jar named {@code
 * Dispatcher.shouldIgnore}'s locals otherwise.  This one runs the same passes
 * before the split and makes the same units, the locals taken in the order
 * of their first use and each local's uses in body order.</p>
 */
final class SharedInitializationSplitter extends BodyTransformer {
    private static final String PHASE = "jb.sils";

    /** Stands in for Soot's phase; before any body is built. */
    static void install() {
        Pack jb = PackManager.v().getPack("jb");
        if (!jb.remove(PHASE)) {
            throw new IllegalStateException("this Soot has no " + PHASE);
        }
        jb.insertAfter(new Transform(PHASE,
                new SharedInitializationSplitter()), "jb.ls");
    }

    @Override
    protected void internalTransform(Body body, String phase,
                                     Map<String, String> options) {
        // Soot's passes before the split, as its phase runs them.
        CopyPropagator.v().transform(body);
        ConstantPropagatorAndFolder.v().transform(body);
        DexNullThrowTransformer.v().transform(body);
        DexNullArrayRefTransformer.v().transform(body);
        FlowSensitiveConstantPropagator.v().transform(body);
        CopyPropagator.v().transform(body);
        DexNullThrowTransformer.v().transform(body);
        DexNullArrayRefTransformer.v().transform(body);
        DeadAssignmentEliminator.v().transform(body);
        CopyPropagator.v().transform(body);
        LocalDefs defs = G.v().soot_toolkits_scalar_LocalDefsFactory()
                .newLocalDefs(ExceptionalUnitGraphFactory
                        .createExceptionalUnitGraph(body,
                                Scene.v().getDefaultThrowAnalysis(),
                                Options.v().omit_excepting_unit_edges()),
                        true);
        // Per local, in order of its first use: each use that only
        // constants reach, with them.
        Map<Local, List<Map.Entry<Unit, List<Unit>>>> clusters =
                new LinkedHashMap<>();
        for (Unit unit : body.getUnits()) {
            for (ValueBox box : unit.getUseBoxes()) {
                Value used = box.getValue();
                if (!(used instanceof Local)) continue;
                List<Unit> reaching = defs.getDefsOfAt((Local) used, unit);
                if (reaching.isEmpty() || !reaching.stream().allMatch(
                        def -> def instanceof AssignStmt
                                && ((AssignStmt) def).getRightOp()
                                instanceof Constant)) {
                    continue;
                }
                clusters.computeIfAbsent((Local) used,
                        ignored -> new ArrayList<>()).add(
                        new AbstractMap.SimpleImmutableEntry<>(unit,
                                reaching));
            }
        }
        int copies = 0;
        for (Map.Entry<Local, List<Map.Entry<Unit, List<Unit>>>> entry
                : clusters.entrySet()) {
            Local local = entry.getKey();
            if (entry.getValue().size() <= 1) continue;
            for (Map.Entry<Unit, List<Unit>> cluster : entry.getValue()) {
                Local copy = (Local) local.clone();
                copy.setName(copy.getName() + '_' + ++copies);
                body.getLocals().add(copy);
                for (Unit constant : cluster.getValue()) {
                    AssignStmt init = (AssignStmt) constant;
                    AssignStmt assign = Jimple.v().newAssignStmt(copy,
                            init.getRightOp());
                    body.getUnits().insertAfter(assign, init);
                    CopyPropagator.copyLineTags(assign.getUseBoxes().get(0),
                            init);
                }
                for (ValueBox box : cluster.getKey().getUseBoxes()) {
                    if (box.getValue() == local) box.setValue(copy);
                }
            }
        }
    }
}
