package edu.uva.liftlab.graphchecker.causynth;

import soot.Body;
import soot.Unit;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.SwitchStmt;
import soot.jimple.TableSwitchStmt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/** Canonical, Soot-CFG-independent identity for one conditional successor. */
final class CausynthBranchShape {
    static final String IF = "IF";
    static final String TABLE_SWITCH = "TABLE_SWITCH";
    static final String LOOKUP_SWITCH = "LOOKUP_SWITCH";

    final String kind;
    final List<Integer> caseKeys;
    final List<Unit> successors;
    final int defaultSuccessorIndex;

    private CausynthBranchShape(String kind, List<Integer> caseKeys,
                                List<Unit> successors,
                                int defaultSuccessorIndex) {
        this.kind = kind;
        this.caseKeys = Collections.unmodifiableList(
                new ArrayList<>(caseKeys));
        this.successors = Collections.unmodifiableList(
                new ArrayList<>(successors));
        this.defaultSuccessorIndex = defaultSuccessorIndex;
    }

    static CausynthBranchShape from(Body body, Unit unit) {
        if (body == null || unit == null) return null;
        if (unit instanceof IfStmt) {
            Unit fallThrough = body.getUnits().getSuccOf(unit);
            Unit taken = ((IfStmt) unit).getTarget();
            if (fallThrough == null || taken == null) return null;
            List<Unit> successors = new ArrayList<>();
            successors.add(fallThrough);
            successors.add(taken);
            return new CausynthBranchShape(IF,
                    Collections.<Integer>emptyList(), successors, -1);
        }
        if (!(unit instanceof SwitchStmt)) return null;

        SwitchStmt branch = (SwitchStmt) unit;
        List<Integer> keys = switchKeys(branch);
        List<Unit> targets = new ArrayList<>(branch.getTargets());
        if (keys.size() != targets.size()
                || branch.getDefaultTarget() == null) {
            return null;
        }
        targets.add(branch.getDefaultTarget());
        String kind = branch instanceof TableSwitchStmt
                ? TABLE_SWITCH : branch instanceof LookupSwitchStmt
                ? LOOKUP_SWITCH : "";
        if (kind.isEmpty()) return null;
        return new CausynthBranchShape(kind, keys, targets,
                targets.size() - 1);
    }

    boolean isSwitch() {
        return TABLE_SWITCH.equals(kind) || LOOKUP_SWITCH.equals(kind);
    }

    int successorCount() {
        return successors.size();
    }

    String encodedCaseKeys() {
        StringBuilder result = new StringBuilder();
        for (Integer key : caseKeys) {
            if (result.length() > 0) result.append(',');
            result.append(key);
        }
        return result.toString();
    }

    private static List<Integer> switchKeys(SwitchStmt branch) {
        List<Integer> result = new ArrayList<>();
        if (branch instanceof TableSwitchStmt) {
            TableSwitchStmt table = (TableSwitchStmt) branch;
            long expected = (long) table.getHighIndex()
                    - (long) table.getLowIndex() + 1L;
            if (expected < 0L || expected != table.getTargets().size()) {
                return Collections.emptyList();
            }
            for (int offset = 0; offset < table.getTargets().size(); offset++) {
                result.add(table.getLowIndex() + offset);
            }
            return result;
        }
        if (branch instanceof LookupSwitchStmt) {
            for (IntConstant key
                    : ((LookupSwitchStmt) branch).getLookupValues()) {
                result.add(key.value);
            }
        }
        return result;
    }
}
