package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * A native reproduction's plant (ADHOC-INFRA WP5.D): the world a confirmed
 * witness ran in, planted in the recording weave on a stock JDK, so a
 * finding is run again without the concolic VM ({@code run_engine.sh}
 * REPRODUCE), and the one question such a run answers: does the planted
 * world take the throw's fatal arm at the claim's anchor.
 *
 * <p>{@code -Dcausynth.plant=<file>} names the plant, JSONL written by
 * CONFIRM's own code ({@code explore.ConfirmMain --plant}), each row
 * numbered ({@value #ROW}); a row the run applied is an {@link #APPLIED}
 * trace row naming its number:</p>
 * <ul>
 *   <li>{@code {"kind":"ROOT","category":"FAULT","rootId",
 *   "occurrence":<occurrence id>,"siteId":<call site>,"value"}}: a marker
 *   call ({@code Debug.makeSymbolicBoolean}) answers the value when its
 *   call site is the row's and a region occurrence enclosing it on this
 *   thread has the row's id -- by {@link OccurrenceAddress#id}, as a
 *   focused replay matches its occurrences -- inside the recording window;
 *   otherwise, and always without a plant, its recorded polarity {@code
 *   false}.  A {@code true} answer is a door fault for the thread's
 *   identity as in a replay ({@link Identity#doorFaulted}).</li>
 *   <li>{@code {"kind":"ROOT","category":"HOOK","rootId","occurrence",
 *   "value"}}: a tree's symbolize hook of that root ({@code
 *   CausynthSymbolicSource.symbolize}) writes the value into the field it
 *   names ({@link RootMint#writeModeledField}) wherever a replay's mint
 *   would plant it ({@code RootMint#focusedRootValue}): under an enclosing
 *   occurrence the confirmation focuses -- the anchor, or the mint
 *   occurrence of any root of the plant ({@link Plant#focused}) -- inside
 *   the window.  A write that fails is an {@link #UNWRITTEN} row.</li>
 *   <li>{@code {"kind":"ORDER","before","after"}}: CONFIRM's own row,
 *   held as a CONFIRM run holds it ({@link Confirmation}, which reads this
 *   file in a planted run): the activation {@code after} enters once those
 *   {@code before} exited.  Held, the row is applied; an activation that
 *   waits is a {@link #HOLDING} row, and one whose wait times out an
 *   {@link #UNHELD} row: what the run states, never a refutation.</li>
 *   <li>{@code {"kind":"TARGET","occurrence":<the anchor's id>,"siteId":
 *   <a TARGET_SITE guard>,"value":<its fatal arm>}} per guard of the
 *   target.  A decision there that takes the fatal arm inside the window is
 *   a {@link #FATAL} trace row, saying whether an enclosing occurrence is
 *   the anchor; at the anchor the run ends ({@link JUnitMethodRunner#exit}),
 *   its question answered, as a focused replay ends at its witness.</li>
 * </ul>
 */
public final class RecordingPlant {
    static final String PROPERTY = "causynth.plant";
    /** The trace event of one plant row applied: a root planted, an order
     *  held. */
    static final String APPLIED = "PLANT_APPLIED";
    /** An ORDER's activation waits for what the model orders before it. */
    static final String HOLDING = "PLANT_HOLDING";
    /** An ORDER the run did not hold within the order's timeout. */
    static final String UNHELD = "PLANT_UNHELD";
    /** A HOOK row reached whose field write failed. */
    static final String UNWRITTEN = "PLANT_UNWRITTEN";
    /** The trace event of one decision of the planted world's fatal arm. */
    static final String FATAL = "PLANT_FATAL";
    /** A root the world assigns, planted where it is minted. */
    public static final String ROOT = "ROOT";
    /** CONFIRM's ORDER row ({@link Confirmation}). */
    public static final String ORDER = "ORDER";
    /** A guard of the target and its fatal arm. */
    public static final String TARGET = "TARGET";
    public static final String KIND = "kind";
    public static final String ROW = "row";
    public static final String CATEGORY = "category";
    public static final String ROOT_ID = "rootId";
    public static final String OCCURRENCE = "occurrence";
    public static final String SITE = "siteId";
    public static final String VALUE = "value";

    /** Read once: the JVM's own property. */
    private static final boolean PLANTING = !file().isEmpty();
    private static volatile Plant plant;
    private static final AtomicBoolean ENDED = new AtomicBoolean();

    private RecordingPlant() {
    }

    /** Whether this run plants a world: a native reproduction, where the
     *  workload's checks of the recording's world do not hold
     *  ({@link CausynthTraceRecorder#replaying}). */
    static boolean planting() {
        return PLANTING;
    }

    /** The plant file this run was handed, or "". */
    static String file() {
        return System.getProperty(PROPERTY, "").trim();
    }

    /** One root of the plant: its row and the value planted. */
    static final class Root {
        final int row;
        final String value;

        Root(int row, String value) {
            this.row = row;
            this.value = value;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Root && ((Root) other).row == row
                    && ((Root) other).value.equals(value);
        }

        @Override
        public int hashCode() {
            return 31 * row + value.hashCode();
        }

        @Override
        public String toString() {
            return row + "=" + value;
        }
    }

    /** One plant file: its roots and its target. */
    static final class Plant {
        /** FAULT markers: call site, then occurrence id, then the root. */
        final Map<String, Map<String, Root>> markers;
        /** HOOK roots, by root id. */
        final Map<String, Root> hooks;
        /** The occurrences the confirmation focuses, by id: the anchor and
         *  every root's mint occurrence ({@code FocusedReplay#focused}). */
        final Set<String> focused;
        /** Guard site -> its fatal arm. */
        final Map<String, Boolean> fatalArms;
        /** The claim's anchor, by occurrence id. */
        final String anchor;

        Plant(Map<String, Map<String, Root>> markers,
              Map<String, Root> hooks, Set<String> focused,
              Map<String, Boolean> fatalArms, String anchor) {
            this.markers = markers;
            this.hooks = hooks;
            this.focused = focused;
            this.fatalArms = fatalArms;
            this.anchor = anchor;
        }
    }

    /** The marker {@code name}'s answer at the call running now. */
    static boolean marker(String name) {
        if (!PLANTING || !RecordingWindow.opened()) return false;
        CausynthTraceRecorder.ActiveCallSiteContext site =
                CausynthTraceRecorder.currentCallSiteContext();
        if (site == null) return false;
        Map<String, Root> rows = plant().markers.get(site.siteId());
        String occurrence = plantedOccurrence(rows,
                CausynthTraceRecorder.enclosingOccurrences());
        if (occurrence == null) return false;
        Root root = rows.get(OccurrenceAddress.parse(occurrence).id());
        boolean value = Boolean.parseBoolean(root.value);
        CausynthTraceRecorder.plantRoot(APPLIED, root.row, name, occurrence,
                String.valueOf(value));
        if (value) Identity.doorFaulted(name);
        return value;
    }

    /** A tree's symbolize hook of {@code rootId} on {@code owner}'s field:
     *  the planted value written there under a focused occurrence. */
    static void hook(String rootId, Object owner, String fieldSignature) {
        if (!PLANTING || !RecordingWindow.opened()) return;
        Plant rows = plant();
        Root root = rows.hooks.get(rootId);
        if (root == null) return;
        String occurrence = focusedOccurrence(rows.focused,
                CausynthTraceRecorder.enclosingOccurrences());
        if (occurrence == null) return;
        CausynthTraceRecorder.plantRoot(RootMint.writeModeledField(owner,
                fieldSignature, "", root.value) ? APPLIED : UNWRITTEN,
                root.row, rootId, occurrence, root.value);
    }

    /** What one ORDER row of the plant came to ({@link Confirmation}):
     *  {@code event} one of {@link #APPLIED}, {@link #HOLDING},
     *  {@link #UNHELD}. */
    static void ordered(String event, int row, String after,
                        String waitingFor) {
        CausynthTraceRecorder.plantOrdered(event, row, after, waitingFor);
    }

    /** A decision the recording observed ({@code outcome} null when it took
     *  no arm a guard names): at a target guard's fatal arm, stated, and at
     *  the anchor the run's end. */
    static void decided(String siteId, Boolean outcome) {
        if (!PLANTING || outcome == null) return;
        Plant rows = plant();
        if (!outcome.equals(rows.fatalArms.get(siteId))
                || !RecordingWindow.opened()) {
            return;
        }
        List<String> enclosing = CausynthTraceRecorder.enclosingOccurrences();
        String anchor = anchorOf(enclosing, rows.anchor);
        CausynthTraceRecorder.plantFatal(siteId, anchor != null ? anchor
                : enclosing.isEmpty() ? "" : enclosing.get(0), anchor != null);
        if (anchor != null && ENDED.compareAndSet(false, true)) {
            end(siteId, anchor);
        }
    }

    /** Of the occurrences enclosing a decision, the anchor's, or null. */
    static String anchorOf(List<String> enclosing, String anchor) {
        for (String occurrence : enclosing) {
            if (OccurrenceAddress.parse(occurrence).id().equals(anchor)) {
                return occurrence;
            }
        }
        return null;
    }

    /** Of the occurrences enclosing a call, innermost first, the first
     *  the confirmation focuses (by id), or null. */
    static String focusedOccurrence(Set<String> focused,
                                    List<String> enclosing) {
        for (String occurrence : enclosing) {
            if (focused.contains(OccurrenceAddress.parse(occurrence).id())) {
                return occurrence;
            }
        }
        return null;
    }

    /** Of the occurrences enclosing a call, innermost first, the first
     *  {@code byOccurrence} plants at (by id), or null. */
    static String plantedOccurrence(Map<String, Root> byOccurrence,
                                    List<String> enclosing) {
        if (byOccurrence == null) return null;
        for (String occurrence : enclosing) {
            if (byOccurrence.containsKey(
                    OccurrenceAddress.parse(occurrence).id())) {
                return occurrence;
            }
        }
        return null;
    }

    /** The run's one end, on a thread of its own: the decision's thread is
     *  the workload's, and the end waits for what is live to settle. */
    private static void end(final String siteId, final String anchor) {
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        new Thread(root, new Runnable() {
            @Override
            public void run() {
                EngineConsole.println("Causynth " + java.time.Instant.now()
                        + ": the native run ends AT_ANCHOR: the planted world"
                        + " took the fatal arm of " + siteId + " at "
                        + anchor);
                JUnitMethodRunner.exit(0);
            }
        }, "causynth-plant-end").start();
    }

    private static Plant plant() {
        Plant rows = plant;
        if (rows != null) return rows;
        synchronized (RecordingPlant.class) {
            if (plant == null) {
                try {
                    plant = read(Paths.get(file()));
                } catch (IOException | RuntimeException unreadable) {
                    // A run told to plant that cannot is no reproduction.
                    throw new IllegalStateException("the plant -D" + PROPERTY
                            + "=" + file() + " is unreadable: "
                            + unreadable.getMessage(), unreadable);
                }
            }
            return plant;
        }
    }

    /**
     * A plant file's roots and target.  A row of another kind, without its
     * number, a ROOT of another category or naming no root, occurrence or
     * value (a FAULT also its call site, and a boolean), a TARGET naming no
     * guard or a boolean arm, and an ORDER naming no activation are
     * refused; so is a plant whose target rows name no anchor or two, since
     * the run would answer nothing.  ORDER rows are {@link Confirmation}'s.
     */
    static Plant read(Path file) throws IOException {
        Map<String, Map<String, Root>> markers =
                new LinkedHashMap<String, Map<String, Root>>();
        Map<String, Root> hooks = new LinkedHashMap<String, Root>();
        Set<String> focused = new LinkedHashSet<String>();
        Map<String, Boolean> fatalArms = new LinkedHashMap<String, Boolean>();
        String anchor = null;
        for (JsonObject row : ArtifactIO.readJsonl(file)) {
            String kind = optionalString(row, KIND);
            if (!row.has(ROW) || !row.get(ROW).isJsonPrimitive()
                    || !row.getAsJsonPrimitive(ROW).isNumber()) {
                throw new IOException("a plant row without its number: "
                        + row);
            }
            int number = row.get(ROW).getAsInt();
            if (ROOT.equals(kind)) {
                focused.add(root(row, number, markers, hooks));
            } else if (TARGET.equals(kind)) {
                String occurrence = optionalString(row, OCCURRENCE);
                if (optionalString(row, SITE).isEmpty()
                        || occurrence.isEmpty() || !row.has(VALUE)
                        || !row.get(VALUE).isJsonPrimitive()
                        || !row.getAsJsonPrimitive(VALUE).isBoolean()) {
                    throw new IOException("not a target row: " + row);
                }
                if (anchor != null && !anchor.equals(occurrence)) {
                    throw new IOException("the plant's target rows name two "
                            + "anchors, " + anchor + " and " + occurrence);
                }
                anchor = occurrence;
                fatalArms.put(optionalString(row, SITE),
                        row.get(VALUE).getAsBoolean());
            } else if (!ORDER.equals(kind)
                    || optionalString(row, "before").isEmpty()
                    || optionalString(row, "after").isEmpty()) {
                throw new IOException("not a plant row: " + row);
            }
        }
        if (anchor == null) {
            throw new IOException("the plant names no target: " + file);
        }
        focused.add(anchor);
        return new Plant(Collections.unmodifiableMap(markers),
                Collections.unmodifiableMap(hooks),
                Collections.unmodifiableSet(focused),
                Collections.unmodifiableMap(fatalArms), anchor);
    }

    /** One ROOT row into the markers or the hooks it plants; returns the
     *  occurrence it is minted at.  A root stated twice is refused. */
    private static String root(JsonObject row, int number,
                               Map<String, Map<String, Root>> markers,
                               Map<String, Root> hooks)
            throws IOException {
        String category = optionalString(row, CATEGORY);
        String rootId = optionalString(row, ROOT_ID);
        String occurrence = optionalString(row, OCCURRENCE);
        String site = optionalString(row, SITE);
        String value = optionalString(row, VALUE);
        boolean fault = RootCategory.FAULT.name().equals(category);
        if (rootId.isEmpty() || occurrence.isEmpty() || value.isEmpty()
                || !(fault || RootCategory.HOOK.name().equals(category))
                || fault && (site.isEmpty() || !("true".equals(value)
                || "false".equals(value)))) {
            throw new IOException("not a root row: " + row);
        }
        Root root = new Root(number, value);
        if (fault) {
            markers.computeIfAbsent(site,
                    key -> new LinkedHashMap<String, Root>())
                    .put(occurrence, root);
        } else if (hooks.put(rootId, root) != null) {
            throw new IOException("the plant states root " + rootId
                    + " twice");
        }
        return occurrence;
    }
}
