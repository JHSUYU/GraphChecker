import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.CountDownLatch;

/**
 * A container a final field holds: mutated in place, never re-pointed, its
 * contents all concrete -- HDFS's {@code BlockTokenSecretManager.allKeys}
 * and {@code BlockPoolManager.bpByBlockPoolId}.  No symbolic value and no
 * symbolic guard ever reaches it, so nothing started its state's log, and a
 * query of it named no version to re-pair.
 *
 * <p>{@code System.observeContainer} starts the log: its INITIAL states what
 * the map held (a stated snapshot of two entries); a later concrete put is a
 * version, and so is the remove() of an iterator the program built before the
 * log began, which no model saw (the tracked state admits it,
 * {@code ContainerSupport::admits}); a query reads the newest version.  A
 * thread outside every region that mutates the map runs bytecode no model
 * sees: its observation just after the mutation marks the log incomplete
 * instead of leaving its chain silently stale, while one after a region
 * thread's mutation does nothing.  Refused: a null (-2), an object that is
 * no container (-12), a container class no model knows (a TreeMap, -12),
 * and outside a region (-1).</p>
 */
public final class RegionContainerObservationSmoke {
    private static final class Manager {
        private final Map<Integer, String> keys =
                new HashMap<Integer, String>();
    }

    private static final class Sink {
        String value;
    }

    public static void main(String[] args) throws Exception {
        final Manager manager = new Manager();
        manager.keys.put(Integer.valueOf(1), "one");
        manager.keys.put(Integer.valueOf(2), "two");
        // An iterator built before the log began: no alias any model knows.
        Iterator<Map.Entry<Integer, String>> walk =
                manager.keys.entrySet().iterator();

        // A thread outside every region, started before any region exists so
        // it inherits none; it mutates once told to.
        final CountDownLatch go = new CountDownLatch(1);
        final int[] outsideStatus = new int[1];
        Thread outside = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    go.await();
                } catch (InterruptedException interrupted) {
                    return;
                }
                manager.keys.put(Integer.valueOf(4), "four");
                outsideStatus[0] = System.observeContainer(manager.keys, true);
            }
        });
        outside.start();

        require(System.observeContainer(manager.keys, false) == -1,
                "observed outside every region");
        require(System.startConcolicRegion("REGION.container-observation",
                "TASK.container-observation") == 0L, "region start rejected");
        require(System.observeContainer(null, false) == -2,
                "a null was observed");
        require(System.observeContainer(new Object(), false) == -12,
                "an object that is no container was observed");
        require(System.observeContainer(new TreeMap<Integer, String>(),
                false) == -12, "an unmodeled container was observed");
        require(System.observeContainer(manager.keys, false) == 0,
                "the container observation failed");
        require(System.observeContainer(manager.keys, false) == 0,
                "a standing log refused its second observation");

        walk.next();
        walk.remove();
        manager.keys.put(Integer.valueOf(3), "three");
        // After a region thread's mutation, which the model versioned.
        require(System.observeContainer(manager.keys, true) == 0,
                "an observation after a modeled mutation was refused");
        Sink sink = new Sink();
        sink.value = manager.keys.get(Integer.valueOf(3));
        String query = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "value", "Ljava/lang/String;",
                sink.value);
        String versions = System.getSharedMapVersions(manager.keys);

        go.countDown();
        outside.join();
        String detected = System.getSharedMapVersions(manager.keys);
        System.endConcolic();

        System.out.println("VERSIONS " + versions);
        System.out.println("QUERY " + query);
        require(versions.contains("\"selected\":true")
                        && versions.contains("\"versionKind\":\"INITIAL\"")
                        && versions.contains("\"stated\":true,\"entries\":2"),
                "the observation stated no INITIAL snapshot: " + versions);
        require(versions.contains("\"versionKind\":\"STATE_REMOVE\""),
                "the iterator's remove() is no version: " + versions);
        require(versions.contains("\"versionKind\":\"STATE_PUT\""),
                "the concrete put is no version: " + versions);
        require(versions.contains("\"writerSetComplete\":true"),
                "the in-region writers are not all named: " + versions);
        require(query.contains("\"_type\":\"ReadFromExpression\"")
                        && query.contains("\"operation\":\"READ\""),
                "the query read no version: " + query);
        require(outsideStatus[0] == -1,
                "the outside thread was observed: " + outsideStatus[0]);
        require(detected.contains("\"writerSetComplete\":false")
                        && detected.contains("UNHOOKED_CONTAINER_MUTATION")
                        && detected.contains("\"unnamedWriter\":true"),
                "the outside mutation is not detected: " + detected);
        System.out.println("CAUSYNTH_REGION_CONTAINER_OBSERVATION_SMOKE_OK");
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
