package edu.uva.liftlab.graphchecker.concolic;

import org.junit.Test;

import java.nio.file.Paths;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

public class ConcolicSchedulerArgumentsTest {
    @Test
    public void parsesOptionalSymbolicRootProposal() {
        ConcolicScheduler.Arguments arguments =
                ConcolicScheduler.Arguments.parse(new String[]{
                        "--region-plan", "plan.jsonl",
                        "--refined-graph", "graph.jsonl.gz",
                        "--symbolic-root-proposal", "proposal.json"
                });
        assertEquals(Paths.get("proposal.json"),
                arguments.symbolicRootProposal);
    }

    @Test
    public void proposalIsAbsentUnlessExplicitlyConfigured() {
        ConcolicScheduler.Arguments arguments =
                ConcolicScheduler.Arguments.parse(new String[]{
                        "--region-plan", "plan.jsonl",
                        "--refined-graph", "graph.jsonl.gz"
                });
        assertNull(arguments.symbolicRootProposal);
    }
}
