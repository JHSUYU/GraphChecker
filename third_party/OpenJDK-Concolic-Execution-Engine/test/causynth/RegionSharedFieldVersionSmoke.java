import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CountDownLatch;

/**
 * Stage 1 of the shared-field work: a selected location records one version
 * per completed write, and nothing else records anything.
 *
 * What this pins down:
 *
 *   1. selection is what turns versioning on.  A field nobody selected reports
 *      no versions at all, on the same object, in the same region, after the
 *      same kind of write.  That is the cost-control claim stated as a test
 *      rather than as a comment: the interpreter hooks fire for every field of
 *      every shadowed object, and only the bounded carrier set pays;
 *   2. selecting publishes an INITIAL version holding the value the location
 *      already had, so the state a later read observes before any tracked
 *      write is an ordinary candidate rather than a hole;
 *   3. each write appends one version carrying its fieldVersionId, the writing
 *      thread's context/region/task evidence, its step, and the expression it
 *      wrote -- symbolic when the value was symbolic, constant when it was
 *      concrete, because a concrete writer is still a competing writer;
 *   4. a write taken on an explicitly marked branch carries that branch as
 *      its path guard, while auxiliary solver constraints remain in the full
 *      path condition and a write taken with no marked branch reports the
 *      empty conjunction explicitly rather than omitting the field;
 *   5. two threads writing one location leave two distinguishable writers;
 *   6. static fields and fixed-shape array elements are addressable the same
 *      way, per class and per index.
 */
public final class RegionSharedFieldVersionSmoke {

    private static final class Holder {
        int seed = 5;
        int shared = 0;
        int untracked = 0;
    }

    private static final class Statics {
        static int shared = 0;
    }

    public static void main(String[] args) throws Exception {
        long status = System.startConcolicRegion(
                "REGION.shared-versions", "TASK.shared-versions");
        require(status == 0L, "region start rejected");

        instanceFieldVersions();
        selectionBoundsTheCarrierSet();
        staticFieldVersions();
        arrayElementVersions();
        twoWritersLeaveTwoWriters();

        System.endConcolic();
        System.out.println("RegionSharedFieldVersionSmoke OK");
    }

    /** (2) (3) (4): initial, symbolic write, concrete write, path guard. */
    private static void instanceFieldVersions() {
        Holder holder = new Holder();
        holder.shared = 41;

        long initial = System.selectSharedFieldCarrier(
                holder, Holder.class.getName(), "shared", "I");
        require(initial > 0L, "carrier selection rejected: " + initial);
        long again = System.selectSharedFieldCarrier(
                holder, Holder.class.getName(), "shared", "I");
        require(again == 0L, "re-selection should be idempotent: " + again);

        String afterSelect = versions(holder, "shared");
        require(afterSelect.contains("\"selected\":true"), afterSelect);
        require(afterSelect.contains("\"writerSetComplete\":true"),
                afterSelect);
        require(afterSelect.contains("\"versionKind\":\"INITIAL\""),
                afterSelect);
        require(count(afterSelect, "\"fieldVersionId\"") == 1, afterSelect);
        // The INITIAL version holds the value the location already had, not a
        // fresh symbol standing in for it.
        require(afterSelect.contains("\"fingerprint\":41"), afterSelect);

        // A concrete write is still a version: it competes with every other
        // writer for a later read.
        holder.shared = 42;
        String afterConcrete = versions(holder, "shared");
        require(count(afterConcrete, "\"fieldVersionId\"") == 2,
                afterConcrete);
        require(afterConcrete.contains("\"versionKind\":\"WRITE\""),
                afterConcrete);
        require(afterConcrete.contains("\"fingerprint\":42"), afterConcrete);
        // No branch has been recorded on this path yet, so the guard is the
        // empty conjunction -- reported, not omitted.
        require(afterConcrete.contains("\"pathGuard\":null"), afterConcrete);
        // Writer evidence is the region this thread was in.
        require(afterConcrete.contains("\"regionId\":\"REGION.shared-versions\""),
                afterConcrete);
        require(afterConcrete.contains("\"taskId\":\"TASK.shared-versions\""),
                afterConcrete);

        // A map observation contributes an auxiliary solver constraint to the
        // full PC.  It must not be copied into this field's writer guard.
        Map<Integer, Object> auxiliary = new HashMap<Integer, Object>();
        auxiliary.put(Integer.valueOf(7), new Object());
        require(System.trackContainerExpression(
                        auxiliary, "SHARED_VERSION_AUX_MAP"),
                "auxiliary map tracking rejected");
        Object observed = auxiliary.get(Integer.valueOf(7));
        require(observed != null, "auxiliary map lookup unexpectedly failed");

        // A symbolic write publishes the expression, and only an explicitly
        // marked branch is copied into the writer-control-guard channel.  The
        // marker must remain the final call before the intended conditional.
        System.symbolizeExactField(
                holder, Holder.class.getName(), "seed", "I", "SEED");
        long branchEvent = System.markConcolicBranch(
                "SHARED.VERSION.GUARD", 1);
        if (holder.seed > 0) {
            holder.shared = holder.seed + 1;
        }
        String fullPath = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String branchEvents = System.getConcolicBranchEvents();
        String afterSymbolic = versions(holder, "shared");
        require(branchEvent > 0L, "writer branch marker rejected");
        require(fullPath.contains("SHARED_VERSION_AUX_MAP"), fullPath);
        require(fullPath.contains("SEED"), fullPath);
        require(fullPath.contains("\"conjunctionInline\":false"),
                fullPath);
        require(!fullPath.contains("TruncatedExpression"), fullPath);
        require(branchEvents.contains("\"siteId\":\"SHARED.VERSION.GUARD\"")
                        && branchEvents.contains("\"conditionCount\":1"),
                branchEvents);
        require(count(afterSymbolic, "\"fieldVersionId\"") == 3,
                afterSymbolic);
        require(afterSymbolic.contains("\"_type\":\"BinaryExpression\""),
                afterSymbolic);
        int guard = afterSymbolic.lastIndexOf("\"pathGuard\":");
        require(guard >= 0 && !afterSymbolic.startsWith(
                        "\"pathGuard\":null", guard),
                "the guarded write should carry its branch: " + afterSymbolic);
        String guardTail = afterSymbolic.substring(guard);
        require(guardTail.contains("SEED"), guardTail);
        require(!guardTail.contains("SHARED_VERSION_AUX_MAP"), guardTail);
        require(afterSymbolic.contains("\"serializationTruncated\":false"),
                afterSymbolic);
        require(!afterSymbolic.contains("TruncatedExpression"),
                afterSymbolic);

        // Version ids come from the session's one event-id space and only ever
        // increase; they are allocation evidence, not a schedule.
        require(firstVersionId(afterSymbolic) == initial, afterSymbolic);
    }

    /** (1): an unselected field of a selected object records nothing. */
    private static void selectionBoundsTheCarrierSet() {
        Holder holder = new Holder();
        require(System.selectSharedFieldCarrier(
                holder, Holder.class.getName(), "shared", "I") > 0L,
                "carrier selection rejected");

        holder.shared = 7;
        holder.untracked = 7;

        String tracked = versions(holder, "shared");
        require(tracked.contains("\"selected\":true"), tracked);
        require(count(tracked, "\"fieldVersionId\"") == 2, tracked);

        String untracked = versions(holder, "untracked");
        require(untracked.contains("\"selected\":false"), untracked);
        require(count(untracked, "\"fieldVersionId\"") == 0, untracked);

        // A field that does not exist is refused rather than silently ignored.
        long missing = System.selectSharedFieldCarrier(
                holder, Holder.class.getName(), "absent", "I");
        require(missing < 0L, "a missing field should be refused: " + missing);
    }

    /** (6): a static field, addressed through its declaring class. */
    private static void staticFieldVersions() {
        Statics.shared = 3;
        long initial = System.selectSharedFieldCarrier(
                Statics.class, Statics.class.getName(), "shared", "I");
        require(initial > 0L, "static selection rejected: " + initial);

        Statics.shared = 9;
        String recorded = System.getSharedFieldVersions(
                Statics.class, Statics.class.getName(), "shared", "I");
        require(recorded.contains("\"locationKind\":\"STATIC_FIELD\""),
                recorded);
        require(count(recorded, "\"fieldVersionId\"") == 2, recorded);
        require(recorded.contains("\"fingerprint\":3"), recorded);
        require(recorded.contains("\"fingerprint\":9"), recorded);
    }

    /** (6): one element of a fixed-shape array, and only that element. */
    private static void arrayElementVersions() {
        int[] slots = new int[]{10, 20, 30};
        long initial = System.selectSharedElementCarrier(slots, 1);
        require(initial > 0L, "element selection rejected: " + initial);

        slots[1] = 21;
        slots[2] = 31;

        String selected = System.getSharedElementVersions(slots, 1);
        require(selected.contains("\"locationKind\":\"ARRAY_ELEMENT\""),
                selected);
        require(selected.contains("\"slot\":1"), selected);
        require(count(selected, "\"fieldVersionId\"") == 2, selected);
        require(selected.contains("\"fingerprint\":20"), selected);
        require(selected.contains("\"fingerprint\":21"), selected);

        String neighbour = System.getSharedElementVersions(slots, 2);
        require(neighbour.contains("\"selected\":false"), neighbour);
        require(count(neighbour, "\"fieldVersionId\"") == 0, neighbour);
    }

    /** (5): two attached threads writing one field stay distinguishable. */
    private static void twoWritersLeaveTwoWriters() throws Exception {
        final Holder holder = new Holder();
        require(System.selectSharedFieldCarrier(
                holder, Holder.class.getName(), "shared", "I") > 0L,
                "carrier selection rejected");

        final CountDownLatch done = new CountDownLatch(2);
        Runnable writer = new Runnable() {
            public void run() {
                long started = System.startConcolicRegion(
                        "REGION.writer", "TASK.writer");
                if (started == 0L) {
                    holder.shared = 77;
                    System.endConcolic();
                }
                done.countDown();
            }
        };
        Thread first = new Thread(writer, "writer-1");
        Thread second = new Thread(writer, "writer-2");
        first.start();
        second.start();
        done.await();
        first.join();
        second.join();

        String recorded = versions(holder, "shared");
        require(count(recorded, "\"fieldVersionId\"") == 3, recorded);
        require(count(recorded, "\"regionId\":\"REGION.writer\"") == 2,
                recorded);
        // The two writes are equal-valued, so nothing but the writer evidence
        // separates them.  That evidence is exactly what Stage 2 needs in
        // order to refuse to guess between them.
        require(count(recorded, "\"fingerprint\":77") == 2, recorded);
        require(distinctWriterContexts(recorded) >= 2,
                "the two writers should be distinguishable: " + recorded);
    }

    private static String versions(Object owner, String field) {
        return System.getSharedFieldVersions(
                owner, Holder.class.getName(), field, "I");
    }

    private static long firstVersionId(String json) {
        int at = json.indexOf("\"fieldVersionId\":");
        require(at >= 0, json);
        int start = at + "\"fieldVersionId\":".length();
        int end = start;
        while (end < json.length() && Character.isDigit(json.charAt(end))) {
            end++;
        }
        return Long.parseLong(json.substring(start, end));
    }

    private static int distinctWriterContexts(String json) {
        java.util.Set<String> seen = new java.util.HashSet<String>();
        String key = "\"writerContextId\":";
        int at = json.indexOf(key);
        while (at >= 0) {
            int start = at + key.length();
            int end = start;
            while (end < json.length()
                    && (Character.isDigit(json.charAt(end))
                        || json.charAt(end) == '-')) {
                end++;
            }
            seen.add(json.substring(start, end));
            at = json.indexOf(key, end);
        }
        return seen.size();
    }

    private static int count(String haystack, String needle) {
        int total = 0;
        int at = haystack.indexOf(needle);
        while (at >= 0) {
            total++;
            at = haystack.indexOf(needle, at + needle.length());
        }
        return total;
    }

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }
}
