/**
 * A field that already carries a symbolic expression is never overwritten by
 * a fresh symbol.  A's field is symbolized, its expression propagates into
 * B's field by plain assignment, and symbolizing B's field afterwards must
 * leave A's symbol in place instead of minting a second, unrelated one.  A
 * field that carries no expression still receives a fresh symbol.
 */
public final class RegionPropagatedFieldGuardSmoke {
    private static volatile int sink;

    private static final class Source {
        int count = 5;
        Object ref = new Object();
    }

    private static final class Sink {
        int count;
        int untouched = 9;
        Object ref;
    }

    public static void main(String[] args) {
        long status = System.startConcolicRegion(
                "REGION.propagated-field-guard", "TASK.propagated-field-guard");
        require(status == 0L, "region start rejected");

        Source a = new Source();
        System.symbolizeField(a, "count", "GUARD.a.count");
        System.symbolizeField(a, "ref", "GUARD.a.ref");

        Sink b = new Sink();
        b.count = a.count;
        b.ref = a.ref;
        if (b.count > 0) sink++;

        // Positive: the propagated expression wins over a fresh symbol.
        System.symbolizeField(b, "count", "GUARD.b.count");
        String count = System.getSymbolicFieldExpression(
                b, Sink.class.getName(), "count", "I",
                Integer.valueOf(b.count));
        require(count.contains("GUARD.a.count"), count);
        require(!count.contains("GUARD.b.count"), count);

        System.symbolizeField(b, "ref", "GUARD.b.ref");
        String ref = System.getSymbolicFieldExpression(
                b, Sink.class.getName(), "ref", "Ljava/lang/Object;", b.ref);
        require(ref.contains("GUARD.a.ref"), ref);
        require(!ref.contains("GUARD.b.ref"), ref);
        String child = System.getSymbolicExpression(b.ref);
        require(child.contains("GUARD.a.ref"), child);
        require(!child.contains("GUARD.b.ref"), child);

        // Negative: a field with no expression still gets a fresh symbol,
        // even on an owner that already carries propagated fields.
        System.symbolizeField(b, "untouched", "GUARD.b.untouched");
        String untouched = System.getSymbolicFieldExpression(
                b, Sink.class.getName(), "untouched", "I",
                Integer.valueOf(b.untouched));
        require(untouched.contains("GUARD.b.untouched"), untouched);
        require(untouched.contains("\"kind\":\"SYMBOLIC_FIELD\""), untouched);

        String summary = System.finishConcolicRegion();
        require(summary.contains("\"complete\":true"), summary);
        System.out.println("CAUSYNTH_REGION_PROPAGATED_FIELD_GUARD_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
