import org.slf4j.helpers.CausynthObservationProbe;

/** Proves that a logging implementation cannot enlarge the workload PC. */
public final class RegionLoggingObservationSmoke {
    private static final class Input {
        int value = 7;
    }

    public static void main(String[] args) {
        Input input = new Input();
        require(System.startConcolicRegion(
                "REGION.logging-observation",
                "TASK.logging-observation") == 0L,
                "region start rejected");
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "LOGGING_SOURCE");

        String before = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        int formatted = CausynthObservationProbe.format(input.value);
        String after = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        require(before.equals(after),
                "logging implementation polluted the workload PC: " + after);
        require(formatted == 130816,
                "logging probe changed concrete execution: " + formatted);

        long event = System.markConcolicBranch("LOGGING.BUSINESS.BRANCH", 1);
        boolean decision = input.value > 0;
        String businessPath = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String branchEvents = System.getConcolicBranchEvents();
        String summary = System.finishConcolicRegion();
        require(event > 0L && decision,
                "business branch did not execute after logging");
        require(branchEvents.contains("LOGGING.BUSINESS.BRANCH")
                        && businessPath.contains("LOGGING_SOURCE"),
                "business branch lost its symbolic source: events="
                        + branchEvents + " path=" + businessPath);
        require(!summary.contains("CausynthObservationProbe")
                        && !summary.contains("TruncatedExpression"),
                "observation sink leaked into summary: " + summary);
        System.out.println("CAUSYNTH_LOGGING_OBSERVATION_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
