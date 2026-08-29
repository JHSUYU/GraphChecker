/** A selected primitive field keeps its source expression across regions. */
public final class RegionCrossActivationPrimitiveFieldSmoke {
    private static final String SOURCE = "SOURCE.cross-activation.expiry";

    private static final class Key {
        long expiry = 7L;
    }

    private static final class Sink {
        long value;
    }

    public static void main(String[] args) {
        long session = System.openWorkloadSession();
        require(session > 0L, "workload session rejected: " + session);

        Key key = new Key();
        require(System.startConcolicRegion("REGION.expiry.r1",
                "TASK.expiry.r1") == 0L, "R1 rejected");
        long r1Context = System.getCurrentConcolicContextId();
        require(r1Context > 0L, "R1 has no VM context identity");
        System.symbolizeExactField(key, Key.class.getName(), "expiry", "J",
                SOURCE);
        require(System.selectSharedFieldCarrier(key, Key.class.getName(),
                "expiry", "J") > 0L, "R1 carrier rejected");
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "R1 summary incomplete");

        require(System.startConcolicRegion("REGION.expiry.r2",
                "TASK.expiry.r2") == 0L, "R2 rejected");
        long r2Context = System.getCurrentConcolicContextId();
        require(r2Context > 0L && r2Context != r1Context,
                "R2 did not receive a distinct VM context identity");
        require(System.selectSharedFieldCarrier(key, Key.class.getName(),
                "expiry", "J") == 0L, "R2 re-selection was not idempotent");
        Sink sink = new Sink();
        sink.value = key.expiry;
        String resumed = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "J",
                Long.valueOf(sink.value));
        require(resumed.contains(SOURCE),
                "R2 lost the R1 field expression: " + resumed);
        System.markConcolicBranch("EXPIRY.REMOVE", 1);
        if (key.expiry < 10L) {
            sink.value++;
        }
        String branches = System.getConcolicBranchEvents();
        require(branches.contains("\"siteId\":\"EXPIRY.REMOVE\"")
                        && branches.contains("\"conditionCount\":1"),
                "R2 branch did not consume the restored field: " + branches);
        require(System.getConcolicPathConditionRange(0, Integer.MAX_VALUE)
                        .contains(SOURCE),
                "R2 path condition lost the R1 root");
        String versions = System.getSharedFieldVersions(key,
                Key.class.getName(), "expiry", "J");
        require(versions.contains("\"resolution\":\"EXACT\""), versions);
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "R2 summary incomplete");
        System.closeWorkloadSession();
        System.out.println("CAUSYNTH_CROSS_ACTIVATION_PRIMITIVE_FIELD_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
