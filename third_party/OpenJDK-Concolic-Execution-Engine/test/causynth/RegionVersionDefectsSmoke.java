import java.util.AbstractList;
import java.util.ArrayList;
import java.util.List;

/**
 * The version log's five defects of vm.md, each closed.
 *
 * <ul>
 *   <li>D2: a container whose first symbolic access wrote it states its
 *       INITIAL as a refusal, never as a stated empty base.</li>
 *   <li>D3: the tracked-location read-out pages by each location's highest
 *       event, so a resume neither repeats nor skips a location.</li>
 *   <li>D4: a reference a thread outside every region stores is a version,
 *       unattributed, naming what it stored.</li>
 *   <li>D5: a concrete store control-dependent on a symbolic decision starts
 *       a scalar field's log, over an INITIAL of the word it replaced.</li>
 *   <li>D7: attaching a container publishes the attached state, and a
 *       version of each tracked element.</li>
 * </ul>
 */
public final class RegionVersionDefectsSmoke {
    private static final class Input {
        int key = 4;
        String name = "abc";
    }

    private static final class Clock {
        int now = 100;
    }

    private static final class Flag {
        int on;
    }

    private static final class Holder {
        String name;
    }

    /** A list the model admits (an AbstractList) and cannot read. */
    private static final class Named extends AbstractList<Object> {
        private final List<Object> backing = new ArrayList<Object>();

        public Object get(int index) {
            return backing.get(index);
        }

        public int size() {
            return backing.size();
        }

        public void add(int index, Object element) {
            backing.add(index, element);
        }
    }

    private static final class ContainerSender {
        Object[] values = new Object[]{"a", "b"};
    }

    private static final class ContainerReceiver {
        Object[] values = new Object[]{"x", "y"};
    }

    private static final String GUARD = "GUARD.D5";

    public static void main(String[] args) throws Exception {
        require(System.startConcolicRegion("REGION.defects",
                "TASK.defects") == 0L, "region start rejected");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "key", "I",
                "DEFECT.KEY");
        System.symbolizeExactField(in, Input.class.getName(), "name",
                "Ljava/lang/String;", "DEFECT.NAME");

        // D2: the list's content is refused by name, not stated empty.
        Named named = new Named();
        named.add(in.name);
        String list = System.getSharedMapVersions(named);
        require(list.contains("\"initialSnapshot\":{\"stated\":false")
                        && list.contains("\"unsupportedClass\""),
                "a refused base reads as stated: " + list);

        // D5.
        Clock clock = new Clock();
        System.symbolizeExactField(clock, Clock.class.getName(), "now", "I",
                "DEFECT.NOW");
        Flag flag = new Flag();
        require(System.installGuardedStoreSites(
                "RegionVersionDefectsSmoke#guarded(LRegionVersionDefectsSmoke"
                        + "$Clock;LRegionVersionDefectsSmoke$Flag;)V\t"
                        + GUARD + "\n") == 1, "table not installed");
        guarded(clock, flag);
        String guardedLog = System.getSharedFieldVersions(flag,
                Flag.class.getName(), "on", "I");
        require(guardedLog.contains("\"versionKind\":\"INITIAL\"")
                        && guardedLog.contains("\"versionKind\":\"WRITE\"")
                        && guardedLog.contains("\"Y_I_0\"")
                        && guardedLog.contains("\"Y_I_1\"")
                        && guardedLog.contains("DEFECT.NOW"),
                "the guarded store started no log: " + guardedLog);

        // D4.
        final Holder holder = new Holder();
        holder.name = in.name;
        Thread outside = new Thread(new Runnable() {
            public void run() {
                holder.name = new String("outside");
            }
        });
        outside.start();
        outside.join();
        String reference = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "name", "Ljava/lang/String;");
        require(count(reference, "\"writerContextId\"") == 2
                        && reference.contains("\"writerContextId\":0")
                        && reference.contains("outside"),
                "the outside reference store is not a version: "
                        + reference);

        // D7.
        ContainerSender sender = new ContainerSender();
        require(System.trackContainerExpression(sender.values, "RPC.values"),
                "array state was not tracked");
        long handle = System.exportExpression(sender,
                ContainerSender.class.getName(), "values",
                "[Ljava/lang/Object;", new long[1]);
        require(handle > 0L, "export rejected: " + handle);
        ContainerReceiver receiver = new ContainerReceiver();
        // A symbolic store tracks the element.
        receiver.values[0] = in.name;
        require(System.attachExpression(receiver,
                ContainerReceiver.class.getName(), "values",
                "[Ljava/lang/Object;", handle, new long[1]) > 0L,
                "attach rejected");
        String state = System.getSharedMapVersions(receiver.values);
        String element = System.getSharedElementVersions(receiver.values, 0);
        require(state.contains("\"versionKind\":\"STATE_ATTACH\""),
                "the attach published no state: " + state);
        require(count(element, "\"writerContextId\"") == 2
                        && element.contains("RPC.values"),
                "the attach published no element version: " + element);

        // D3: pages of one location each, resumed, meet every location once.
        java.util.Set<String> seen = new java.util.HashSet<String>();
        long after = 0L;
        int pages = 0;
        while (true) {
            String page = System.getTrackedLocationVersions(after, 1);
            pages++;
            int offset = 0;
            String key = "\"selected\":true,\"location\":{";
            while ((offset = page.indexOf(key, offset)) >= 0) {
                int end = page.indexOf('}', offset);
                String location = page.substring(offset, end);
                require(seen.add(location), "a page repeated " + location);
                offset = end;
            }
            if (page.contains("\"complete\":true")) break;
            long next = number(page, "\"nextAfterEventId\":");
            require(next > after, "the resume went back: " + next + " after "
                    + after);
            after = next;
            require(pages < 10000, "the read-out did not end");
        }
        require(seen.size() >= 4 && pages >= 4,
                "the read-out paged " + pages + " times over " + seen.size());

        System.endConcolic();
        System.out.println("RegionVersionDefectsSmoke OK");
    }

    private static void guarded(Clock clock, Flag flag) {
        long marked = System.markConcolicBranch(GUARD, 1);
        if (clock.now > 50) {
            flag.on = 1;
        }
        require(marked > 0L, "branch marker rejected");
    }

    private static long number(String json, String key) {
        int at = json.indexOf(key);
        require(at >= 0, key + " absent: " + json);
        int from = at + key.length();
        int to = from;
        while (to < json.length() && (Character.isDigit(json.charAt(to))
                || json.charAt(to) == '-')) {
            to++;
        }
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
