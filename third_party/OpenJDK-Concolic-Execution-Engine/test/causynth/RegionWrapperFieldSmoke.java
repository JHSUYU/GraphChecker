/**
 * A wrapper-typed field holds a value.
 *
 * <p>A Long field is a value cell: a box is immutable and a store puts a new
 * one, so what a reader observes is the long (or null).  SOLR-18413 keeps its
 * routing rule's expiry in RoutingRule.expireAt, and the observer refused the
 * field on every woven access.  It is observed, stored and read as its box's
 * primitive word, or the null word: a symbolic box stores its value, a
 * concrete one its constant, null the null reference; a read is the value's
 * sort, and its unboxing reads the read.</p>
 */
public final class RegionWrapperFieldSmoke {
    private static final class Input {
        long t = 1000L;
    }

    private static final class Rule {
        Long expireAt;
    }

    private static final class Sink {
        long j;
    }

    public static void main(String[] args) {
        Rule rule = new Rule();
        // One symbolic session across both regions.
        require(System.openWorkloadSession() > 0L, "no workload session");
        require(System.startConcolicRegion("REGION.wrapper.write",
                "TASK.wrapper") == 0L, "region start rejected");
        System.observeField(rule, Rule.class.getName(),
                "expireAt", "Ljava/lang/Long;");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "t", "J",
                "WRAP.T");
        rule.expireAt = Long.valueOf(in.t);
        System.endConcolic();

        require(System.startConcolicRegion("REGION.wrapper.read",
                "TASK.wrapper") == 0L, "region start rejected");
        Sink sink = new Sink();
        Long read = rule.expireAt;
        sink.j = read.longValue();
        String symbolic = field(sink);
        require(sink.j == 1000L && symbolic.contains("WRAP.T")
                        && symbolic.contains("\"_java_type\":\"J\"")
                        && symbolic.contains("\"observedExact\":true"),
                "the unboxed read is not the stored value: " + symbolic);

        rule.expireAt = Long.valueOf(7L);
        sink.j = rule.expireAt.longValue();
        String constant = field(sink);
        require(constant.contains("\"Y_J_7\"")
                        && constant.contains("\"observedExact\":true")
                        && !constant.contains("WRAP.T"),
                "the concrete box is not its constant: " + constant);

        rule.expireAt = null;
        Long nothing = rule.expireAt;
        require(nothing == null, "null did not store");
        String log = System.getSharedFieldVersions(rule, Rule.class.getName(),
                "expireAt", "Ljava/lang/Long;");
        System.endConcolic();
        require(System.closeWorkloadSession() == 0L, "session not closed");
        require(count(log, "\"writerContextId\"") == 4
                        && log.contains("\"versionKind\":\"INITIAL\"")
                        && !log.contains("UNOBSERVED")
                        && log.contains("\"writerSetComplete\":true"),
                "the wrapper log is not INITIAL, WRITE x3: " + log);
        System.out.println("RegionWrapperFieldSmoke OK");
    }

    private static String field(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "j", "J", Long.valueOf(sink.j));
    }

    private static int count(String value, String needle) {
        int result = 0;
        int offset = 0;
        while ((offset = value.indexOf(needle, offset)) >= 0) {
            result++;
            offset += needle.length();
        }
        return result;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
