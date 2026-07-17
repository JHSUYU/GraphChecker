package concolic.test.symbolic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class RegionApiTest {
    @Test
    void snapshotsNamedRegionAndOutputExpressionBeforeCleanup() {
        Integer value = 42;
        System.startConcolicRegion("REGION.test", "ACT.test");
        System.symbolize(value, "region_test_input");

        if (value.intValue() > 0) {
            // Record one graph-relevant path predicate.
        }

        String expression = System.getSymbolicExpression(value);
        String liveSummary = System.getConcolicRegionSummary();
        String finishedSummary = System.finishConcolicRegion();

        assertTrue(expression.contains("\"symbolic\":true"));
        assertTrue(expression.contains("\"expression\":"));
        assertTrue(liveSummary.contains("\"regionId\":\"REGION.test\""));
        assertTrue(liveSummary.contains("\"activationId\":\"ACT.test\""));
        assertTrue(liveSummary.contains("\"pathCondition\":["));
        assertTrue(finishedSummary.contains("\"regionId\":\"REGION.test\""));
    }
}
