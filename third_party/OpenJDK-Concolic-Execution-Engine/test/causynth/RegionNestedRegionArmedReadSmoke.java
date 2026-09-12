/**
 * Nesting contract for armed replay reads.
 *
 * <p>Regions nest on one thread context.  An arm is a one-shot override of
 * the read its arming region is about to perform, so closing an INNER region
 * must abandon what the inner region armed and leave the enclosing region's
 * arms pending.  Purging every arm of the thread context at each region
 * boundary broke the first half; keeping them all past the arming region's
 * close would break the second.</p>
 */
public final class RegionNestedRegionArmedReadSmoke {
    private static final int REPLAY_READ_UNKNOWN_TOKEN = -7;

    private static final class Holder {
        int outerField = 7;
        int innerField = 9;
    }

    private static final class Sink {
        int value;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion(
                "REGION.outer", "TASK.outer") == 0L,
                "outer region start rejected");

        Holder holder = new Holder();
        select(holder, "outerField", "NESTED.OUTER");
        select(holder, "innerField", "NESTED.INNER");

        long outerReceipt = System.armSharedPrimitiveFieldRead(holder,
                Holder.class.getName(), "outerField", "I", 41L);
        require(outerReceipt > 0L, "the outer region's read was not armed");

        // An inner region opens, arms a read of its own and closes, all
        // between the outer arm and the read it overrides.
        require(System.startConcolicRegion(
                "REGION.inner", "TASK.inner") == 0L,
                "inner region start rejected");
        long innerReceipt = System.armSharedPrimitiveFieldRead(holder,
                Holder.class.getName(), "innerField", "I", 55L);
        require(innerReceipt > 0L, "the inner region's read was not armed");
        require(System.endConcolic() == 0L, "inner region end rejected");

        // The inner region's own arm is abandoned by its close.
        Sink abandoned = new Sink();
        abandoned.value = holder.innerField;
        require(abandoned.value == 9,
                "a read armed by a region that has ended was consumed: "
                        + abandoned.value);
        require(System.confirmSharedPrimitiveFieldRead(innerReceipt)
                        == REPLAY_READ_UNKNOWN_TOKEN,
                "an abandoned receipt is still known");

        // The enclosing region's arm is not: its own region is still open.
        Sink survived = new Sink();
        survived.value = holder.outerField;
        require(survived.value == 41,
                "closing an inner region dropped the enclosing region's "
                        + "armed read: " + survived.value);
        require(System.confirmSharedPrimitiveFieldRead(outerReceipt) > 0L,
                "the enclosing region's read did not consume its receipt");

        System.endConcolic();
        System.out.println("RegionNestedRegionArmedReadSmoke OK");
    }

    private static void select(Holder holder, String field, String symbol) {
        System.symbolizeExactField(holder, Holder.class.getName(), field,
                "I", symbol);
        require(System.selectSharedFieldCarrier(holder,
                Holder.class.getName(), field, "I") > 0L,
                "carrier selection rejected for " + field);
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
