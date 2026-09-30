/**
 * Contract smoke for bounded shared reads.
 *
 * <p>One concrete execution performs one real read, and at that instant the
 * location held exactly one version.  The read node names that version and
 * carries its value; the writers the run did not read are retained in the
 * location's log, where a later question can still find them, and are not
 * republished as arms of the read.  {@code writerSetComplete} stays separate
 * coverage metadata about that log.</p>
 */
public final class RegionSharedReadFromSmoke {
    private static final class Holder {
        int shared = 7;
        int unselected;
    }

    private static final class Input {
        int value = 3;
    }

    private static final class Sink {
        int value;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion(
                "REGION.read-from", "TASK.read-from") == 0L,
                "region start rejected");

        Holder holder = new Holder();
        System.symbolizeExactField(holder, Holder.class.getName(), "shared",
                "I", "READ.INIT");

        Input input = new Input();
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "READ.NEXT");
        require(System.markConcolicBranch("READ.WRITE", 1) > 0L,
                "branch marker rejected");
        if (input.value > 0) {
            holder.shared = input.value + 1;
        }

        require(holder.unselected == 0, "an unselected field moved");
        Sink second = new Sink();
        second.value = holder.shared;
        require(second.value == 4, "the guarded store did not run: "
                + second.value);
        String multiple = expression(second);
        require(multiple.contains(
                "\"expressionAuthority\":\"VM_GUARDED_READ_FROM_V1\""),
                multiple);
        require(multiple.contains("\"writerSetComplete\":true"), multiple);
        // The word the read loaded is the word its observed version stored.
        require(multiple.contains("\"observedExact\":true"), multiple);
        // The value the read carries is the writer it observed, computed from
        // READ.NEXT.  The mint it did not read is not in the read at all.
        require(multiple.contains("READ.NEXT"), multiple);
        require(!multiple.contains("READ.INIT"), multiple);

        String evidence = System.getSharedFieldVersions(
                holder, Holder.class.getName(), "shared", "I");
        require(evidence.contains("\"selected\":true"), evidence);
        require(evidence.contains("\"writerSetComplete\":true"), evidence);
        // Both writers stay in the log -- one version entry each, and only a
        // version entry carries a writerContextId.
        require(count(evidence, "\"writerContextId\"") == 2, evidence);
        require(evidence.contains("READ.INIT"), evidence);
        require(evidence.contains("READ.NEXT"), evidence);
        // The version the read named is the newest retained one, and the
        // older one is named by no read.
        require(namesVersion(multiple, versionId(evidence, true)),
                "the read did not name the newest retained writer: "
                        + multiple + " over " + evidence);
        require(!namesVersion(multiple, versionId(evidence, false)),
                "the read published a writer it did not observe: " + multiple);
        // One read of this location, and only a read entry carries a reader.
        require(count(evidence, "\"readerContextId\"") == 1, evidence);

        String unselected = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "unselected", "I");
        require(unselected.contains("\"selected\":false"), unselected);

        everyRecordStatesItsSite(evidence, multiple);

        System.endConcolic();
        System.out.println("RegionSharedReadFromSmoke OK");
    }

    /**
     * Every logged read and write states the bytecode site it stood at, and
     * the read node states the same one.
     *
     * <p>Identity v3 addresses an endpoint by {@code (occurrence, site,
     * siteIndex, attempt)}, and the innermost frame of a read's or a write's
     * site index is a bytecode site only the VM stands at.  The log used to
     * state none, so two reads of one location by one occurrence at different
     * places in the code were indistinguishable: 38 of 46 ReadRows and 50 of
     * 52 WriteRows of the 17960 seed carried an empty site index, and the
     * anchor's two reads of {@code MAP_STATE/1#-3} collapsed onto one
     * endpoint id, which the explorer then read as a replacement.</p>
     *
     * <p>The site is components, never a rendered id: the consumer spells
     * the method part its own way and has to be the only place that does.</p>
     */
    private static void everyRecordStatesItsSite(String evidence,
                                                 String read) {
        System.out.println("READ_LOG " + evidence);
        System.out.println("EVENT_ID " + System.currentSymbolicEventId());

        // Four records state a site here: the two writers, the read record,
        // and the read node the expression table holds -- and every one of
        // them is in this method, so nothing states a site by accident.
        require(count(evidence, "\"site\":{") == 4, evidence);
        require(count(evidence, SITE) == 4,
                "not every logged read and write stated its site: "
                        + evidence);
        require(read.contains(SITE),
                "the read node stated no site: " + read);

        // The read record and the read node name the SAME site: one read,
        // one place, stated identically by the log and by the expression.
        String reads = section(evidence, "\"reads\":[");
        require(count(reads, SITE) == 1, reads);
        int where = bciAfter(reads, SITE);
        require(read.contains(SITE + where + "}"),
                "the read log and the read node disagree about where the"
                        + " read ran: " + reads + " vs " + read);
        // Two guarded reads reach this value -- of the other input inside the
        // guarded store, and of the shared field -- and each states its own
        // site, which is how they are told apart at all.
        require(count(read, SITE) == 2, read);

        // Four different places in this one method: the mint's call site,
        // the read of the other input inside the guarded store, the store
        // itself, and this load.  This is the whole point -- two events of
        // ONE location are told apart by where they ran, which a location
        // key and an occurrence id cannot do.  None is 0: neither a store
        // nor a load sits at the method entry, and an unstated site is
        // absent rather than bci 0.
        require(distinctBcis(evidence) == 4,
                "the log did not tell its events apart by site: " + evidence);
        require(bciAfter(evidence, SITE) > 0, evidence);
        require(bciAfter(read, SITE) > 0, read);

        // The event id is read-only and bounds the log, which is what lets a
        // caller's own journal say which log events happened inside one of
        // its frames.
        long now = System.currentSymbolicEventId();
        require(System.currentSymbolicEventId() == now,
                "currentSymbolicEventId published an event of its own");
        require(now > 0L, "no event was published: " + now);
        require(versionId(evidence, true) <= now,
                "a version id exceeded the published event id: " + now);
    }

    /** The one spelling every record of this run's sites must carry. */
    private static final String SITE = "\"site\":{\"className\":"
            + "\"RegionSharedReadFromSmoke\",\"methodName\":\"main\","
            + "\"methodDescriptor\":\"([Ljava/lang/String;)V\",\"bci\":";

    /** One flat array of the envelope, from `start` to its close. */
    private static String section(String json, String start) {
        int at = json.indexOf(start);
        require(at >= 0, start + " is absent from " + json);
        int end = json.indexOf(']', at);
        require(end > at, json);
        return json.substring(at, end);
    }

    /** How many different bcis the sites in `json` name. */
    private static int distinctBcis(String json) {
        String key = "\"bci\":";
        StringBuilder seen = new StringBuilder(",");
        int count = 0;
        int offset = 0;
        while ((offset = json.indexOf(SITE, offset)) >= 0) {
            int from = json.indexOf(key, offset) + key.length();
            int to = from;
            while (to < json.length() && json.charAt(to) >= '0'
                    && json.charAt(to) <= '9') {
                to++;
            }
            String bci = "," + json.substring(from, to) + ",";
            if (seen.indexOf(bci) < 0) {
                seen.append(bci.substring(1));
                count++;
            }
            offset = to;
        }
        return count;
    }

    /** The bci of the first site in `json`. */
    private static int bciAfter(String json, String site) {
        int at = json.indexOf(site);
        require(at >= 0, json);
        int from = at + site.length();
        int to = from;
        while (to < json.length() && json.charAt(to) >= '0'
                && json.charAt(to) <= '9') {
            to++;
        }
        require(to > from, json);
        return Integer.parseInt(json.substring(from, to));
    }

    private static String expression(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "value", "I", Integer.valueOf(sink.value));
    }

    /** Whether any read node in `json` names `versionId` as its observed one. */
    private static boolean namesVersion(String json, long versionId) {
        return json.contains("\"observedVersion\":{\"fieldVersionId\":"
                + versionId + ",");
    }

    /**
     * The newest (or oldest) entry of the `versions` array, which ends where
     * the read log begins.  Read from the log rather than assumed, so the
     * comparison below is between two things the VM said.
     */
    private static long versionId(String json, boolean newest) {
        int end = json.indexOf("],\"readLogTruncated\"");
        require(end >= 0, "no version log in " + json);
        String key = "\"fieldVersionId\":";
        int at = newest ? json.lastIndexOf(key, end) : json.indexOf(key);
        require(at >= 0 && at < end, "no versions in " + json);
        int from = at + key.length();
        int to = from;
        while (to < json.length() && json.charAt(to) >= '0'
                && json.charAt(to) <= '9') {
            to++;
        }
        require(to > from, json);
        return Long.parseLong(json.substring(from, to));
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
