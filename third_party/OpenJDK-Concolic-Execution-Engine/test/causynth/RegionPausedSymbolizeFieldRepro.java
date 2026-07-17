/**
 * Diagnostic companion to RegionPausedSymbolizationSmoke.  It prints the
 * native symbolic-state and path-condition snapshots for an unpaused
 * baseline and for pause -> symbolizeField -> resume -> branch.
 */
public final class RegionPausedSymbolizeFieldRepro {
    private static final class Input {
        int value = 7;
    }

    private static volatile int sink;

    public static void main(String[] args) {
        Result baseline = run(false, "repro_unpaused_value", false);
        Result paused = run(true, "repro_paused_value", true);
        Result pausedNoProbe = run(true, "repro_paused_no_probe_value",
                false);

        print("BASELINE_AFTER_SYMBOLIZE", baseline.afterSymbolize);
        print("BASELINE_EXPRESSION", baseline.expression);
        print("BASELINE_AFTER_BRANCH", baseline.afterBranch);
        print("PAUSED_AFTER_SYMBOLIZE", paused.afterSymbolize);
        print("PAUSED_EXPRESSION", paused.expression);
        print("PAUSED_AFTER_RESUME", paused.afterResume);
        print("PAUSED_AFTER_BRANCH", paused.afterBranch);
        print("PAUSED_NO_PROBE_AFTER_BRANCH", pausedNoProbe.afterBranch);

        require(has(baseline.expression, "\"symbolic\":true"),
                "baseline native explicit symbolization failed");
        require(hasNonEmptyPc(baseline.afterBranch),
                "baseline Java branch instrumentation failed");
        require(has(paused.afterSymbolize,
                "\"pathConditionPauseDepth\":1"),
                "explicit native call did not preserve pause depth");
        require(has(paused.expression, "\"symbolic\":true"),
                "paused native explicit symbolization failed");
        require(has(paused.afterResume,
                "\"pathConditionPauseDepth\":0"),
                "resume did not restore pause depth to zero");
        require(hasNonEmptyPc(paused.afterBranch),
                "post-resume Java branch instrumentation failed");
        require(has(paused.afterBranch, "repro_paused_value"),
                "post-resume PC does not use the paused native field symbol");
        require(has(pausedNoProbe.expression, "\"symbolic\":true"),
                "paused/no-probe native explicit symbolization failed");
        require(hasNonEmptyPc(pausedNoProbe.afterBranch),
                "paused/no-probe Java branch instrumentation failed");
        require(has(pausedNoProbe.afterBranch,
                "repro_paused_no_probe_value"),
                "paused/no-probe PC does not use the native field symbol");
        require(sink == 3, "unexpected sink=" + sink);
        System.out.println(
                "CAUSYNTH_REGION_PAUSED_SYMBOLIZE_FIELD_REPRO_OK");
    }

    private static Result run(boolean pause, String prefix,
                              boolean probeAfterResume) {
        Input input = new Input();
        Result result = new Result();
        long started = System.startConcolicRegion(
                pause ? "REGION.repro.paused" : "REGION.repro.unpaused",
                pause ? "ACT.repro.paused" : "ACT.repro.unpaused");
        require(started == 0L, "region start rejected: " + started);
        boolean paused = false;
        try {
            if (pause) {
                System.pauseConcolicPathCondition();
                paused = true;
            }
            System.symbolizeField(input, "value", prefix);
            result.afterSymbolize = System.getConcolicRegionSummary();
            result.expression = System.getSymbolicExpression(input);
            if (pause) {
                System.resumeConcolicPathCondition();
                paused = false;
                if (probeAfterResume) {
                    result.afterResume = System.getConcolicRegionSummary();
                }
            }
            if (input.value > 0) {
                sink++;
            }
            result.afterBranch = System.getConcolicRegionSummary();
        } finally {
            if (paused) {
                System.resumeConcolicPathCondition();
            }
            System.finishConcolicRegion();
        }
        return result;
    }

    private static boolean hasNonEmptyPc(String summary) {
        return summary != null
                && summary.indexOf("\"pathCondition\":[{") >= 0;
    }

    private static boolean has(String text, String fragment) {
        return text != null && text.indexOf(fragment) >= 0;
    }

    private static void print(String label, String value) {
        System.out.println(label + "=" + value);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }

    private static final class Result {
        String afterSymbolize;
        String expression;
        String afterResume;
        String afterBranch;
    }
}
