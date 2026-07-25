package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Canonical branch and non-branch replay evidence extracted from one summary.
 *
 * <p>The branch contract is the only runtime branch authority.  The solver
 * context contains only positioned, non-branch constraints.  Keeping the two
 * immutable values together prevents schedulers from rebuilding a second
 * target-branch protocol out of loosely related JSON fields.</p>
 */
public final class BranchReplayPlan {
    private final BranchReplayContract replayContract;
    private final SolverPathContext solverPathContext;

    private BranchReplayPlan(BranchReplayContract replayContract,
                             SolverPathContext solverPathContext) {
        this.replayContract = replayContract;
        this.solverPathContext = solverPathContext;
    }

    public static BranchReplayPlan fromSummary(JsonObject summary,
                                               String siteId,
                                               int occurrence) {
        List<SummaryBranchMapping> mappings =
                SummaryBranchMapping.fromSummary(summary);
        SummaryBranchMapping selected = null;
        for (SummaryBranchMapping mapping : mappings) {
            if (siteId.equals(mapping.siteId())
                    && occurrence == mapping.occurrence()) {
                if (selected != null) {
                    throw new IllegalArgumentException(
                            "target branch mapping is not unique");
                }
                selected = mapping;
            }
        }
        if (selected == null) {
            throw new IllegalArgumentException(
                    "target branch mapping is missing");
        }
        return fromSummary(summary, mappings, selected);
    }

    static BranchReplayPlan fromSummary(
            JsonObject summary, List<SummaryBranchMapping> mappings,
            SummaryBranchMapping selected) {
        if (selected == null || !selected.isWitnessed()) {
            throw new IllegalArgumentException(
                    "target branch has no immutable witness");
        }
        JsonArray path = summary.getAsJsonArray("pathCondition");
        int targetPosition = selected.summaryPcIndex();
        BranchWitness source = selected.witness();

        List<SummaryBranchMapping> prefixMappings = new ArrayList<>();
        for (SummaryBranchMapping mapping : mappings) {
            if (mapping.isWitnessed()
                    && mapping.summaryPcIndex() < targetPosition) {
                prefixMappings.add(mapping);
            }
        }
        Collections.sort(prefixMappings, Comparator.comparingInt(
                SummaryBranchMapping::summaryPcIndex));

        List<BranchWitness> prefix = new ArrayList<>();
        Set<Integer> branchPositions = new LinkedHashSet<>();
        for (SummaryBranchMapping mapping : prefixMappings) {
            int position = mapping.summaryPcIndex();
            if (!branchPositions.add(position)) {
                throw new IllegalArgumentException(
                        "branch witness prefix does not partition the path");
            }
            prefix.add(mapping.witness());
        }
        return new BranchReplayPlan(BranchReplayContract.flip(prefix, source),
                SolverPathContext.fromPath(path, branchPositions,
                        targetPosition));
    }

    public BranchReplayContract replayContract() {
        return replayContract;
    }

    public SolverPathContext solverPathContext() {
        return solverPathContext;
    }

}
