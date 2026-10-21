import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Symbolic arithmetic summaries for AtomicInteger and AtomicLong RMW calls; a
 * compareAndSet that lost answers `old == expected` over the expected value
 * its caller passed.
 */
public final class RegionAtomicApiSmoke {
    private RegionAtomicApiSmoke() {
    }

    private static final class Sink {
        boolean lost;
    }

    public static void main(String[] args) {
        long status = System.startConcolicRegion(
                "REGION.atomic", "TASK.atomic");
        require(status == 0L, "region start rejected");

        AtomicInteger intValue = new AtomicInteger(2);
        System.observeField(
                intValue, AtomicInteger.class.getName(), "value", "I");
        int oldInt = intValue.getAndDecrement();
        int newInt = intValue.get();
        Sink sink = new Sink();
        sink.lost = intValue.compareAndSet(7, 9);

        AtomicLong longValue = new AtomicLong(5L);
        System.observeField(
                longValue, AtomicLong.class.getName(), "value", "J");
        long oldLong = longValue.getAndDecrement();
        long newLong = longValue.get();

        require(oldInt == 2 && newInt == 1 && !sink.lost
                        && oldLong == 5L && newLong == 4L,
                "unexpected concrete atomic results");

        Integer oldIntBox = new Integer(oldInt);
        Integer newIntBox = new Integer(newInt);
        Long oldLongBox = new Long(oldLong);
        Long newLongBox = new Long(newLong);
        System.pauseConcolicPathCondition();
        String oldIntExpression = System.getSymbolicExpression(oldIntBox);
        String newIntExpression = System.getSymbolicExpression(newIntBox);
        String oldLongExpression = System.getSymbolicExpression(oldLongBox);
        String newLongExpression = System.getSymbolicExpression(newLongBox);
        String intFieldExpression = System.getSymbolicFieldExpression(
                intValue, AtomicInteger.class.getName(), "value", "I",
                Integer.valueOf(newInt));
        String longFieldExpression = System.getSymbolicFieldExpression(
                longValue, AtomicLong.class.getName(), "value", "J",
                Long.valueOf(newLong));
        String lostExpression = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "lost", "Z",
                Boolean.valueOf(sink.lost));
        System.resumeConcolicPathCondition();
        String summary = System.finishConcolicRegion();

        requireConstant(oldIntExpression, "Y_I_2");
        requireConstant(oldLongExpression, "Y_J_5");
        requireDecrement(newIntExpression, "Y_I_2");
        requireDecrement(newLongExpression, "Y_J_5");
        requireCapturedMutationValue(intFieldExpression, "Y_I_2");
        requireCapturedMutationValue(longFieldExpression, "Y_J_5");
        require(lostExpression.contains("\"_op\":\"==\"")
                        && lostExpression.contains("Y_I_7"),
                "a failed compareAndSet compared another word than its"
                        + " expected value: " + lostExpression);
        require(summary.contains("\"complete\":true"), summary);
        System.out.println("CAUSYNTH_REGION_ATOMIC_API_SMOKE_OK");
    }

    private static void requireDecrement(String expression, String symbol) {
        require(expression.contains(symbol)
                        && expression.contains(
                        "\"_type\":\"BinaryExpression\"")
                        && expression.contains("\"_op\":\"-\""),
                expression);
    }

    private static void requireConstant(String expression, String constant) {
        require(expression.contains("\"_type\":\"ConstExpr\"")
                        && expression.contains(constant)
                        && !expression.contains("SymbolExpression"),
                expression);
    }

    private static void requireCapturedMutationValue(
            String expression, String symbol) {
        require(expression.contains("\"symbolic\":true")
                        && expression.contains(
                        "\"expressionAuthority\":\"VM_EXACT_FIELD_SHADOW_V1\"")
                        && !expression.contains("SymbolExpression"),
                expression);
        requireDecrement(expression, symbol);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
