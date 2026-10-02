import java.util.ArrayList;
import java.util.List;

/**
 * Contract smoke for engine state a new thread inherits
 * (GraphChecker's runtime.InheritedState).
 *
 * <p>{@code Thread.init} runs an {@code InheritableThreadLocal}'s
 * {@code childValue} on the creator, inside the creator's region.  The
 * engine's computes the child's identity from a list of the creator's
 * objects; one of them carries a value (a box of a symbolic int), so the list
 * is a tracked container.  Walked with the VM's propagation paused, as
 * InheritedState walks it, the child still inherits, and the creator's plain
 * object is left as it was; walked unpaused, the same walk names that object
 * by a NEXT relation over the list, and every later read of its fields would
 * be a projection.</p>
 */
public final class RegionInheritedStateSmoke {
    private static final class Input {
        int n;
    }

    private static final class Plain {
        int k = 1;
    }

    private static final class Inherited
            extends InheritableThreadLocal<Integer> {
        private final List<Object> receivers;
        private final boolean paused;

        Inherited(List<Object> receivers, boolean paused) {
            this.receivers = receivers;
            this.paused = paused;
        }

        @Override
        protected Integer childValue(Integer parent) {
            if (paused) System.pauseConcolicPathCondition();
            try {
                int count = 0;
                for (Object receiver : receivers) {
                    if (receiver != null) count++;
                }
                return parent + count;
            } finally {
                if (paused) System.resumeConcolicPathCondition();
            }
        }
    }

    public static void main(String[] args) throws Exception {
        require(System.startConcolicRegion("REGION.inherited",
                "TASK.inherited") == 0L, "region start rejected");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "n", "I",
                "INHERITED.N");

        Plain kept = new Plain();
        List<Object> pausedReceivers = new ArrayList<Object>();
        pausedReceivers.add(Integer.valueOf(in.n));
        pausedReceivers.add(kept);
        Plain named = new Plain();
        List<Object> unpausedReceivers = new ArrayList<Object>();
        unpausedReceivers.add(Integer.valueOf(in.n + 1));
        unpausedReceivers.add(named);

        final Inherited paused = new Inherited(pausedReceivers, true);
        final Inherited unpaused = new Inherited(unpausedReceivers, false);
        paused.set(Integer.valueOf(10));
        unpaused.set(Integer.valueOf(20));
        final int[] inherited = new int[2];
        Thread child = new Thread(new Runnable() {
            @Override
            public void run() {
                inherited[0] = paused.get().intValue();
                inherited[1] = unpaused.get().intValue();
            }
        });
        String keptExpression = System.getSymbolicExpression(kept);
        String namedExpression = System.getSymbolicExpression(named);
        child.start();
        child.join();
        System.endConcolic();

        require(inherited[0] == 12 && inherited[1] == 22,
                "the child did not inherit: " + inherited[0] + ", "
                        + inherited[1]);
        require(namedExpression.contains("\"operation\":\"NEXT\""),
                "the unpaused walk named nothing, so this smoke shows"
                        + " nothing: " + namedExpression);
        require(!keptExpression.contains("\"operation\":\"NEXT\""),
                "the paused walk named the creator's object: "
                        + keptExpression);
        System.out.println("RegionInheritedStateSmoke OK");
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
