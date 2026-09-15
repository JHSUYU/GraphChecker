import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Contract smoke for a concrete write that is control-dependent on a
 * symbolic decision.
 *
 * <p>A container becomes a symbolic state variable at its first
 * symbolic-or-guarded write.  Until now only a symbolic <em>value</em>
 * started a log, so a concrete mutation of a concrete container left no
 * version even when the program only performed it on one arm of a symbolic
 * branch.  HDFS-11741 is that shape: {@code removeExpiredKeys()} removes
 * concrete, pre-recording keys from a concrete map under
 * {@code expiryDate < now}, where {@code now} is a declared CLOCK root, and
 * the removal of the Balancer's key -- the causal crux -- was invisible.</p>
 *
 * <p>What the map holds after that removal is a function of the predicate, so
 * the removal is evidence: the log starts at it, over a stated base, and a
 * later {@code get} reads through the versioned state.  On the other arm the
 * removal does not run, nothing about the map depends on anything symbolic,
 * and it stays untracked -- being reachable from a guarded branch is not
 * enough, running there is.</p>
 */
public final class RegionGuardedConcreteWriteSmoke {
    private static final class Clock {
        int now;

        Clock(int now) {
            this.now = now;
        }
    }

    public static void main(String[] args) {
        String removed = run(true);
        String kept = run(false);

        // The arm that removed: the log starts at the REMOVE, over a base the
        // recording stated, and the read resolves through it.
        require(removed.contains("\"selected\":true"), removed);
        require(removed.contains("\"versionKind\":\"INITIAL\""), removed);
        require(removed.contains("\"versionKind\":\"STATE_REMOVE\""), removed);
        require(removed.contains("\"stated\":true"), removed);
        require(removed.contains("\"entries\":2"), removed);
        require(removed.contains("\"operation\":\"REMOVE\""), removed);
        // The REMOVE stands on the base the recording stated, not on an
        // opaque root: that is what makes "what the map holds now"
        // resolvable at all.  REMOVE(SNAPSHOT_BASE(PUT, PUT)) is the chain.
        require(removed.contains("\"operation\":\"SNAPSHOT_BASE\""), removed);
        require(removed.contains("\"operation\":\"STATE\""), removed);
        // Both later queries -- the containsKey and the get -- resolved over
        // the log, which is what reading through the versioned state means.
        // An untracked map answers them concretely and records no read at
        // all, which is what the other arm shows.
        require(count(removed, "\"readerContextId\"") == 2, removed);

        // The arm that did not: no version, nothing tracked.
        require(kept.contains("\"selected\":false"), kept);
        require(!kept.contains("\"fieldVersionId\""), kept);
        require(!kept.contains("\"readerContextId\""), kept);

        System.out.println(
                "CAUSYNTH_REGION_GUARDED_CONCRETE_WRITE_SMOKE_OK");
    }

    /**
     * One replay of the same program, on one arm of the symbolic decision.
     *
     * <p>Everything about the map is concrete: the entries predate the
     * region, the key removed is a concrete key, and the value read back is a
     * concrete value.  The only symbolic thing in the method is the clock the
     * branch tests.</p>
     */
    private static String run(boolean expired) {
        require(System.startConcolicRegion("REGION.guarded-write."
                + expired, "TASK.guarded-write") == 0L,
                "region start rejected");

        Map<Integer, String> keys = new LinkedHashMap<Integer, String>();
        keys.put(Integer.valueOf(1), "balancer");
        keys.put(Integer.valueOf(2), "namenode");

        Clock clock = new Clock(expired ? 100 : 1);
        System.symbolizeExactField(clock, Clock.class.getName(), "now", "I",
                "CLOCK.now");
        // Marked immediately before the branch, with nothing in between, the
        // way the weaving emits it: a reserved exact branch event is
        // finalized by the very next conditional bytecode, so comparing the
        // marker's own result would consume the reservation and the branch
        // that followed would contribute no guard.
        // The plan's answer, installed the way the runtime installs it: this
        // method's stores are control-dependent on GUARD_SITE, and nothing
        // else in this program is control-dependent on anything.  A store in
        // a method the table does not name never starts a log, which is what
        // keeps a decision from admitting every store that merely follows it.
        require(System.installGuardedStoreSites(STORE_SITES) == 1,
                "the guarded-store table was not installed");
        long marked = System.markConcolicBranch(GUARD_SITE, 1);
        if (clock.now > 50) {
            // Concrete removal of a concrete key from a concrete map, taken
            // because a symbolic predicate came out one way.
            keys.remove(Integer.valueOf(1));
        }
        require(marked > 0L, "branch marker rejected");
        // A callee reached from the guarded branch, storing concretely into a
        // container of its own.  Its method is not in the table, so nothing
        // it does starts a log -- which is the whole difference between
        // control dependence and "after a decision".  17960's seed logged
        // eleven such sites (DigestBase#engineUpdate, HeapByteBuffer#_put,
        // FileSummary$Section#getSerializedSize, UnmodifiableList#get) and
        // the explorer read them as six BLOCKING TOPOLOGY_DIVERGENCE.
        Map<Integer, String> downstream = serializeLike(expired);

        require(keys.containsKey(Integer.valueOf(2)),
                "the wrong entry was removed");
        require(keys.get(Integer.valueOf(1)) == null || !expired,
                "the removal did not run concretely");

        String followed = System.getSharedMapVersions(downstream);
        require(followed.contains("\"selected\":false"),
                "a concrete store in a callee of the guarded branch started a"
                        + " log: " + followed);
        require(!followed.contains("\"fieldVersionId\""), followed);

        String evidence = System.getSharedMapVersions(keys);
        System.out.println((expired ? "REMOVED " : "KEPT ") + evidence);
        System.endConcolic();
        return evidence;
    }

    /**
     * Concrete stores in another method, reached from the guarded branch.
     *
     * <p>This is the shape of the protobuf serialization internals 17960's
     * anchor reaches after its own decision: every store here is concrete,
     * none of them is control-dependent on anything, and none of them may
     * start a log.</p>
     */
    private static Map<Integer, String> serializeLike(boolean expired) {
        Map<Integer, String> buffer = new LinkedHashMap<Integer, String>();
        for (int index = 0; index < 4; index++) {
            buffer.put(Integer.valueOf(index), expired ? "e" : "k");
        }
        return buffer;
    }

    /**
     * A real woven guard site id: a Soot signature followed by its unit
     * index, whose parameter list contains commas.  Splitting the guard list
     * on commas fragmented 15 of 27 of these and they matched nothing, so the
     * table's fields are tab-separated and nothing else is a separator.
     */
    private static final String GUARD_SITE =
            "<org.apache.hadoop.hdfs.server.namenode.snapshot.SnapshotManager:"
                    + " java.lang.String createSnapshot(org.apache.hadoop"
                    + ".hdfs.server.namenode.INodesInPath,java.lang.String,"
                    + "long)>#u11";

    /**
     * This method's stores, and the branches they are control-dependent on:
     * the method key, then one field per guard site.  Two guards here, so the
     * second field is not the last -- a parser that stopped at the first tab,
     * or split a field on its commas, fails this.
     */
    private static final String STORE_SITES =
            "RegionGuardedConcreteWriteSmoke#run(Z)Ljava/lang/String;"
                    + "\t" + GUARD_SITE
                    + "\t<some.Other: void m(int,long)>#u3";

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
