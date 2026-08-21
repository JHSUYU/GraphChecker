/** Verifies nullable-reference and symbolic-reference branch ownership. */
public final class RegionReferenceBranchApiSmoke {
    private static final class Input {
        // Package-private on purpose: Java 8 otherwise lowers the enclosing
        // class access through a synthetic access$... method, which tests
        // arbitrary method-return shadow propagation instead of the
        // getfield -> ifnull/if_acmp bytecode pair covered by this smoke.
        Object left;
        Object right;

        Input(Object left, Object right) {
            this.left = left;
            this.right = right;
        }
    }

    public static void main(String[] args) {
        Trace nullSeed = executeNullBranch(null, "nullable_null");
        require(nullSeed.result == 1, nullSeed.summary);
        require(nullSeed.path.contains("nullable_null")
                        && nullSeed.path.contains("\"_op\":\"==\"")
                        && nullSeed.path.contains("\"_exp\":\"N\""),
                nullSeed.path);
        // javac lowers the early true arm to ifnonnull; for a null seed the
        // JVM conditional is not taken even though the source predicate is
        // true.  BranchEvent.outcome intentionally reports JVM control flow.
        requireExactEvent(nullSeed.events, "REF.NULL.nullable_null", false,
                1);

        Trace nonNullSeed = executeNullBranch(new Object(),
                "nullable_non_null");
        require(nonNullSeed.result == 0, nonNullSeed.summary);
        require(nonNullSeed.path.contains("nullable_non_null")
                        && nonNullSeed.path.contains("\"_op\":\"!=\"")
                        && nonNullSeed.path.contains("\"_exp\":\"N\""),
                nonNullSeed.path);
        requireExactEvent(nonNullSeed.events,
                "REF.NULL.nullable_non_null", true, 1);

        Trace distinct = executeReferenceComparison(new Object(),
                new Object(), "distinct_refs");
        require(distinct.result == 0, distinct.summary);
        require(distinct.path.contains("reference_left_distinct_refs")
                        && distinct.path.contains(
                        "reference_right_distinct_refs")
                        && distinct.path.contains("\"_op\":\"!=\""),
                distinct.path);
        requireExactEvent(distinct.events, "REF.ACMP.distinct_refs", true,
                1);
        System.out.println("CAUSYNTH_REGION_REFERENCE_BRANCH_API_SMOKE_OK");
    }

    private static Trace executeNullBranch(Object seed, String suffix) {
        Input input = new Input(seed, new Object());
        require(System.startConcolicRegion("REGION.reference-null",
                "ACT." + suffix) == 0L, "region start rejected");
        System.symbolizeField(input, "left", suffix);
        long event = System.markConcolicBranch("REF.NULL." + suffix, 1);
        int result;
        if (input.left == null) {
            result = 1;
        } else {
            result = 0;
        }
        require(event > 0L, "branch marker rejected");
        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String events = System.getConcolicBranchEvents();
        String summary = System.finishConcolicRegion();
        return new Trace(result, summary, events, path);
    }

    private static Trace executeReferenceComparison(Object left, Object right,
                                                    String suffix) {
        Input input = new Input(left, right);
        require(System.startConcolicRegion("REGION.reference-acmp",
                "ACT." + suffix) == 0L, "region start rejected");
        System.symbolizeField(input, "left",
                "reference_left_" + suffix);
        System.symbolizeField(input, "right",
                "reference_right_" + suffix);
        long event = System.markConcolicBranch("REF.ACMP." + suffix, 1);
        int result;
        if (input.left == input.right) {
            result = 1;
        } else {
            result = 0;
        }
        require(event > 0L, "branch marker rejected");
        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String events = System.getConcolicBranchEvents();
        String summary = System.finishConcolicRegion();
        return new Trace(result, summary, events, path);
    }

    private static void requireExactEvent(String events, String site,
                                          boolean outcome, int count) {
        require(events.contains("\"siteId\":\"" + site + "\"")
                        && events.contains("\"occurrence\":1")
                        && events.contains("\"outcome\":" + outcome)
                        && events.contains("\"conditionIndices\":[")
                        && !events.contains("\"conditionIndices\":[]")
                        && events.contains("\"conditionCount\":" + count),
                events);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }

    private static final class Trace {
        final int result;
        final String summary;
        final String events;
        final String path;

        Trace(int result, String summary, String events, String path) {
            this.result = result;
            this.summary = summary;
            this.events = events;
            this.path = path;
        }
    }
}
