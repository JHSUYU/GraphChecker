import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Contract smoke for a removal performed through a container view.
 *
 * <p>A view -- entrySet/keySet/values and the iterators over them -- is never
 * a location of its own: a mutation through one is a mutation of the BACKING
 * container.  This is HDFS-11741's {@code removeExpiredKeys()}
 * (BlockTokenSecretManager:224-233) exactly: the loop walks
 * {@code allKeys.entrySet().iterator()}, every read in it is concrete, and the
 * only symbolic thing is {@code getExpiryDate() < now} with {@code now} a
 * declared CLOCK root.  The removal of the Balancer's key is the causal crux,
 * so it has to reach the map's chain as {@code REMOVE(key)} -- with the key
 * taken from the entry the iterator last returned, which is concrete in the
 * iterator's own field, so the reads need no admission and the iterator needs
 * no chain of its own.</p>
 */
public final class RegionViewRemovalSmoke {
    private static final class Key {
        final long expiry;

        Key(long expiry) {
            this.expiry = expiry;
        }

        long getExpiryDate() {
            return expiry;
        }
    }

    private static final class Clock {
        long now;

        Clock(long now) {
            this.now = now;
        }
    }

    public static void main(String[] args) {
        String removed = run(500L);
        String kept = run(0L);

        // The arm that removed: the map's own chain gains the removal, over a
        // base the recording stated, and a later get reads through it.
        require(removed.contains("\"selected\":true"), removed);
        require(removed.contains("\"locationKind\":\"MAP_STATE\""), removed);
        require(removed.contains("\"versionKind\":\"INITIAL\""), removed);
        require(removed.contains("\"stated\":true"), removed);
        require(removed.contains("\"entries\":2"), removed);
        require(removed.contains("\"operation\":\"SNAPSHOT_BASE\""), removed);
        // One REMOVE version per expired entry, on the map's location -- not
        // on a location of the iterator's own.
        require(count(removed, "\"versionKind\":\"STATE_REMOVE\"") == 1,
                "the view removal did not reach the map's chain: " + removed);
        require(removed.contains("\"operation\":\"REMOVE\""), removed);
        // The later get of the removed key resolved over the log.
        require(count(removed, "\"readerContextId\"") >= 1, removed);

        // The other arm: nothing expired, so nothing about the map depends on
        // anything symbolic and it stays untracked.
        require(kept.contains("\"selected\":false"), kept);
        require(!kept.contains("\"fieldVersionId\""), kept);
        require(!kept.contains("\"readerContextId\""), kept);

        System.out.println("CAUSYNTH_REGION_VIEW_REMOVAL_SMOKE_OK");
    }

    private static String run(long now) {
        require(System.startConcolicRegion("REGION.view-removal." + now,
                "TASK.view-removal") == 0L, "region start rejected");

        Map<Integer, Key> allKeys = new LinkedHashMap<Integer, Key>();
        allKeys.put(Integer.valueOf(1), new Key(100L));
        allKeys.put(Integer.valueOf(2), new Key(900L));

        Clock clock = new Clock(now);
        System.symbolizeExactField(clock, Clock.class.getName(), "now", "J",
                "CLOCK.now");

        // The plan's answer, installed the way the runtime installs it: the
        // removal in this method is control-dependent on GUARD.expiry.
        require(System.installGuardedStoreSites(STORE_SITES) == 1,
                "the guarded-store table was not installed");

        // BTSM:224-233, unchanged in shape.
        Iterator<Map.Entry<Integer, Key>> it =
                allKeys.entrySet().iterator();
        int visit = 0;
        while (it.hasNext()) {
            Map.Entry<Integer, Key> entry = it.next();
            // One occurrence per visit: a reservation is per site AND
            // occurrence, so reusing one would be refused as a duplicate.
            // Marked immediately before the branch, as the weaving emits it.
            visit++;
            System.markConcolicBranch("GUARD.expiry", visit);
            if (entry.getValue().getExpiryDate() < clock.now) {
                it.remove();
            }
        }
        require(visit == 2, "the loop did not visit both entries: " + visit);

        require(allKeys.containsKey(Integer.valueOf(2)),
                "the unexpired entry was removed");
        require(allKeys.get(Integer.valueOf(1)) == null || now == 0L,
                "the expired entry was not removed concretely");

        String evidence = System.getSharedMapVersions(allKeys);
        System.out.println((now > 0L ? "REMOVED " : "KEPT ") + evidence);
        System.endConcolic();
        return evidence;
    }

    /** This method's stores, and the branch they are control-dependent on. */
    private static final String STORE_SITES =
            "RegionViewRemovalSmoke#run(J)Ljava/lang/String;"
                    + "\tCALL remove\tGUARD.expiry";

    private static int count(String value, String needle) {
        int result = 0;
        int offset = 0;
        while ((offset = value.indexOf(needle, offset)) >= 0) {
            result++;
            offset += needle.length();
        }
        return result;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
