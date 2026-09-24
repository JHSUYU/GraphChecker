/**
 * A shared-state event names the bytecode that made it, on every execution.
 *
 * <p>The VM reads an event's site off the frame, and this interpreter keeps
 * pc in a register and writes it back only at calls.  So a field read was
 * named by the last call before it -- except on the one execution that
 * resolved its constant-pool entry through the VM, which wrote pc back: one
 * read had two names, two reads with no call between them had one, and a
 * hook woven before an access named the hook.  Here both reads are resolved
 * before the region opens and each then runs twice.</p>
 */
public final class RegionEventSiteSmoke {
    private static final class Holder {
        int first = 2;
        int second = 3;
    }

    /** Where {@link #reads} stands; its two getfields are at 1 and 5. */
    private static final String SITE = "\"site\":{\"className\":"
            + "\"RegionEventSiteSmoke\",\"methodName\":\"reads\","
            + "\"methodDescriptor\":\"(LRegionEventSiteSmoke$Holder;)I\","
            + "\"bci\":";

    public static void main(String[] args) {
        Holder holder = new Holder();
        int sum = reads(holder);
        require(System.startConcolicRegion("REGION.site", "TASK.site") == 0L,
                "region start rejected");
        System.symbolizeExactField(holder, Holder.class.getName(), "first",
                "I", "SITE.FIRST");
        System.symbolizeExactField(holder, Holder.class.getName(), "second",
                "I", "SITE.SECOND");
        for (int turn = 0; turn < 2; turn++) sum += reads(holder);
        require(sum == 15, "the reads returned " + sum);

        String first = section(System.getSharedFieldVersions(holder,
                Holder.class.getName(), "first", "I"), "\"reads\":[");
        String second = section(System.getSharedFieldVersions(holder,
                Holder.class.getName(), "second", "I"), "\"reads\":[");
        require(count(first, SITE) == 2 && count(second, SITE) == 2,
                "each read was not logged twice at its site: " + first
                        + " / " + second);
        require(bcis(first).equals(",1,1,"),
                "the first getfield is not named by itself: " + first);
        require(bcis(second).equals(",5,5,"),
                "the second getfield is not named by itself: " + second);

        System.endConcolic();
        System.out.println("RegionEventSiteSmoke OK");
    }

    /** Two field reads with no call between them. */
    private static int reads(Holder holder) {
        return holder.first + holder.second;
    }

    /** One flat array of the envelope, from `start` to its close. */
    private static String section(String json, String start) {
        int at = json.indexOf(start);
        require(at >= 0, start + " is absent from " + json);
        int end = json.indexOf(']', at);
        require(end > at, json);
        return json.substring(at, end);
    }

    /** Every bci the sites in `json` name, in order: ",b1,b2,". */
    private static String bcis(String json) {
        StringBuilder named = new StringBuilder(",");
        int offset = 0;
        while ((offset = json.indexOf(SITE, offset)) >= 0) {
            int from = offset + SITE.length();
            int to = from;
            while (to < json.length() && json.charAt(to) >= '0'
                    && json.charAt(to) <= '9') {
                to++;
            }
            named.append(json, from, to).append(',');
            offset = to;
        }
        return named.toString();
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
