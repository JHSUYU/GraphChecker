import java.lang.reflect.Method;

public final class RegionApiSmoke {
    public static void main(String[] args) throws Exception {
        Integer value = Integer.valueOf(42);
        Method pause = System.class.getMethod("pauseConcolicPathCondition");
        Method resume = System.class.getMethod("resumeConcolicPathCondition");
        System.startConcolicRegion("REGION.smoke", "ACT.smoke");
        System.symbolize(value, "smoke_input");
        if (value.intValue() > 0) {
            // Force one symbolic branch into the path condition.
        }
        pauseObservation(pause);
        String beforeBookkeeping = System.getPathCondition();
        boolean ignoredDecision = bookkeeping(value, pause, resume);
        require(ignoredDecision, "bookkeeping result");
        String duringBookkeeping = System.getPathCondition();
        require(beforeBookkeeping.equals(duringBookkeeping),
                duringBookkeeping);
        resumeObservation(resume);
        if (value.intValue() < 100) {
            // Recording resumes for the next real target condition.
        }
        pause.invoke(null);
        String afterTarget = System.getPathCondition();
        require(!beforeBookkeeping.equals(afterTarget), afterTarget);
        String expression = System.getSymbolicExpression(value);
        String summary = System.finishConcolicRegion();
        require(expression.contains("\"symbolic\":true"), expression);
        require(summary.contains("\"regionId\":\"REGION.smoke\""), summary);
        require(summary.contains("\"taskId\":\"ACT.smoke\""), summary);
        require(summary.contains("\"pathCondition\":["), summary);
        require(summary.contains("\"pathConditionRecordingPaused\":true"),
                summary);
        System.out.println("CAUSYNTH_REGION_API_SMOKE_OK");
    }

    private static void pauseObservation(Method pause) throws Exception {
        pause.invoke(null);
    }

    private static void resumeObservation(Method resume) throws Exception {
        resume.invoke(null);
    }

    private static boolean bookkeeping(Integer value, Method pause,
                                       Method resume) throws Exception {
        boolean result = value.intValue() == 42;
        pause.invoke(null);
        if (value.intValue() != 0) {
            result = result && true;
        }
        resume.invoke(null);
        if (value.intValue() > -1) {
            result = result && true;
        }
        return result;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
