package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WorldRefutation;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.setting;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class FocusedReplay {
    private static final Object LOCK = new Object();
    private static boolean loaded;
    private static Task task;
    private static final List<Obligation> OBLIGATIONS =
            new ArrayList<Obligation>();
    private static final Map<String, String> REFUSALS =
            new LinkedHashMap<String, String>();
    private static final Set<String> FLIPPED = new LinkedHashSet<String>();
    private static final Set<String> FOCUSED_TASKS =
            new LinkedHashSet<String>();
    private static final Set<String> FOCUSED_OCCURRENCES =
            new LinkedHashSet<String>();
    private static final Set<String> ROOT_MINTS =
            new LinkedHashSet<String>();

    private static final class Inherited {
        private final String at;
        private final String siteId;
        private final int ordinal;
        private final boolean outcome;
        private final String obligationId;
        private boolean taken;
        private String refusal = "";

        private Inherited(String at, String siteId, int ordinal,
                          boolean outcome, String obligationId) {
            this.at = at;
            this.siteId = siteId;
            this.ordinal = ordinal;
            this.outcome = outcome;
            this.obligationId = obligationId;
        }

        private String render() {
            return siteId + "#" + ordinal + " -> " + outcome
                    + " at occurrence " + at + " (obligation "
                    + obligationId + ")";
        }
    }

    private static final List<Inherited> INHERITED =
            new ArrayList<Inherited>();

    private static final Set<String> INHERITED_OCCURRENCES =
            new LinkedHashSet<String>();

    private FocusedReplay() {
    }

    private static String declaredTarget = "";

    static boolean declaredTarget(OccurrenceAddress occurrence) {
        load();
        if (occurrence == null) return false;
        synchronized (LOCK) {
            return !declaredTarget.isEmpty()
                    && declaredTarget.equals(occurrence.render());
        }
    }

    public static boolean focused(OccurrenceAddress occurrence) {
        load();
        if (occurrence == null) return false;
        synchronized (LOCK) {
            if (FOCUSED_OCCURRENCES.contains(occurrence.render())
                    || ROOT_MINTS.contains(occurrence.id())
                    || INHERITED_OCCURRENCES.contains(occurrence.id())) {
                return true;
            }
        }
        if (task == null || task.focused() == null) return false;
        if (occurrence.equals(task.focused())) return true;
        if (task.factor() == null) return false;
        for (OccurrenceAddress member : task.factor()) {
            if (occurrence.equals(member)) return true;
        }
        return false;
    }

    public static boolean focused(String taskId, OccurrenceAddress occurrence) {
        load();
        if (occurrence == null) return false;
        String id = trimmed(taskId);
        synchronized (LOCK) {
            if (!id.isEmpty() && FOCUSED_TASKS.contains(id)) {
                FOCUSED_OCCURRENCES.add(occurrence.render());
                return true;
            }
        }
        boolean declared = focused(occurrence);
        if (declared) {
            synchronized (LOCK) {
                FOCUSED_OCCURRENCES.add(occurrence.render());
            }
        }
        return declared;
    }

    public static Long clockSkew(String rootId) {
        load();
        String stated = CLOCK_DELTAS.get(trimmed(rootId));
        if (stated == null) return null;
        try {
            return Long.valueOf(stated);
        } catch (NumberFormatException notASkew) {
            return null;
        }
    }

    private static final Map<String, String> CLOCK_DELTAS =
            new LinkedHashMap<String, String>();

    public static String rootAssignment(String rootId) {
        load();
        String id = trimmed(rootId);
        for (Obligation obligation : OBLIGATIONS) {
            if (obligation.rootAssignments() == null) continue;
            String value = obligation.rootAssignments().get(id);
            if (value != null) return value;
        }
        return "";
    }

    public static String answer(String endpointId) {
        load();
        String id = trimmed(endpointId);
        for (Obligation obligation : OBLIGATIONS) {
            if (obligation.answers() == null) continue;
            String value = obligation.answers().get(id);
            if (value != null) return value;
        }
        return "";
    }

    public static boolean observeDecision(OccurrenceAddress occurrence,
                                          String siteId, int ordinal,
                                          boolean outcome) {
        load();
        if (task == null || occurrence == null) return false;
        String at = occurrence.id();
        boolean decided = false;
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                observe(obligation, at, siteId, ordinal, outcome);
            }
            for (Inherited flip : INHERITED) {
                if (flip.taken || !flip.refusal.isEmpty()) continue;
                if (!flip.at.equals(at)) continue;
                if (!flip.siteId.equals(trimmed(siteId))
                        || flip.ordinal != ordinal) {
                    continue;
                }
                if (outcome == flip.outcome) {
                    flip.taken = true;
                    continue;
                }
                flip.refusal = "wrong decision at " + flip.siteId + "#"
                        + flip.ordinal + " of occurrence " + flip.at
                        + ": took " + outcome + ", the flip this replay "
                        + "INHERITED from the session its path was cut "
                        + "from is " + flip.render();
                decided |= decide(flip.refusal);
            }
        }
        return decided;
    }

    private static String refusedAt = "";

    private static boolean decide(String refusal) {
        if (!refusedAt.isEmpty() || OBLIGATIONS.isEmpty()) return false;
        refusedAt = refusal;
        return true;
    }

    static final String REPLAY_NO_PROGRESS = "REPLAY_NO_PROGRESS";

    private static String stalledAt = "";

    static boolean noProgress(String what, String held) {
        if (confirming()) return false;
        synchronized (LOCK) {
            if (workloadEnded || !refusedAt.isEmpty()
                    || !stalledAt.isEmpty()) {
                return false;
            }
            String stall = REPLAY_NO_PROGRESS + ": " + trimmed(what) + "; "
                    + (held.isEmpty() ? "no schedule hold was live"
                    : "a schedule hold was live: " + held);
            if (FLIPPED.isEmpty()) return decide(stall);
            stalledAt = stall;
            return true;
        }
    }

    static boolean stalledAfterFlip() {
        synchronized (LOCK) {
            return !stalledAt.isEmpty();
        }
    }

    static String refusedAt() {
        load();
        synchronized (LOCK) {
            return refusedAt;
        }
    }

    private static void observe(Obligation obligation, String at,
                                String siteId, int ordinal,
                                boolean outcome) {
        String id = trimmed(obligation.obligationId());
        if (REFUSALS.containsKey(id) || FLIPPED.contains(id)) return;
        if (!trimmed(FOCUS.get(id)).equals(trimmed(at))) return;
        if (!trimmed(obligation.siteId()).equals(trimmed(siteId))
                || obligation.ordinal() != ordinal) {
            return;
        }
        if (outcome == obligation.flippedOutcome()) {
            FLIPPED.add(id);
            return;
        }
        REFUSALS.put(id, "wrong decision at " + trimmed(siteId)
                + "#" + ordinal + " of occurrence " + trimmed(at)
                + ": took " + outcome + ", the obligation flips it to "
                + obligation.flippedOutcome());
    }

    static void viewRead(Endpoint reader, long version) {
        load();
        if (task == null || reader == null) return;
        String id = Confirmation.id(reader);
        String because = Confirmation.untakenBecause(id);
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                String asked = trimmed(obligation.obligationId());
                if (!obligation.pairing()
                        || !obligation.pairedReader().equals(id)
                        || REFUSALS.containsKey(asked)
                        || FLIPPED.contains(asked)) {
                    continue;
                }
                if (version == obligation.pairedVersion()) {
                    FLIPPED.add(asked);
                } else {
                    REFUSALS.put(asked, PAIRING_UNTAKEN + ": read " + id
                            + " observed version " + version + " of its"
                            + " view, the pairing flip asks version "
                            + obligation.pairedVersion()
                            + (because.isEmpty() ? "" : " (" + because + ")"));
                }
            }
        }
    }

    private static final Map<String, String> FOCUS =
            new LinkedHashMap<String, String>();

    public static boolean contradicted(OccurrenceAddress occurrence) {
        load();
        if (task == null || occurrence == null) return false;
        synchronized (LOCK) {
            return !refused(occurrence.id()).isEmpty();
        }
    }

    public static String refusal(OccurrenceAddress occurrence) {
        load();
        if (task == null || occurrence == null) return "";
        synchronized (LOCK) {
            return refused(occurrence.id());
        }
    }

    private static String refused(String at) {
        for (Obligation obligation : OBLIGATIONS) {
            String id = trimmed(obligation.obligationId());
            if (!trimmed(FOCUS.get(id)).equals(trimmed(at))) continue;
            String detail = REFUSALS.get(id);
            if (detail != null) return detail;
        }
        return "";
    }

    public static boolean complete(OccurrenceAddress occurrence) {
        load();
        if (task == null || occurrence == null) return true;
        if (!focused(occurrence)) return true;
        String at = occurrence.id();
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                String id = trimmed(obligation.obligationId());
                if (!trimmed(FOCUS.get(id)).equals(trimmed(at))) continue;
                if (!FLIPPED.contains(id)) return false;
            }
            return true;
        }
    }

    private static String unmatchedPrefix = "";

    private static final String PREFIX_UNMATCHED = "REPLAY_PREFIX_UNMATCHED";

    static final String PAIRING_UNTAKEN = "PAIRING_UNTAKEN";

    static boolean noteUnansweredTask(String detail) {
        String stated = trimmed(detail);
        if (!stated.startsWith(PREFIX_UNMATCHED)) return false;
        load();
        synchronized (LOCK) {
            if (!unmatchedPrefix.isEmpty()) return false;
            unmatchedPrefix = stated;
            return decide(stated);
        }
    }

    private static String unsettledPublication = "";

    static boolean unsettled() {
        synchronized (LOCK) {
            return !unsettledPublication.isEmpty();
        }
    }

    static void noteUnsettledPublication(String detail) {
        load();
        synchronized (LOCK) {
            if (unsettledPublication.isEmpty()) {
                unsettledPublication = trimmed(detail);
            }
        }
    }

    private static final Set<String> MINTED = new LinkedHashSet<String>();

    static void mintPublished(String rootId) {
        String id = trimmed(rootId);
        if (id.isEmpty()) return;
        load();
        synchronized (LOCK) {
            MINTED.add(id);
        }
    }

    public static List<ObligationResult> results(String sessionId) {
        load();
        List<ObligationResult> results = new ArrayList<ObligationResult>();
        if (task == null) return results;
        List<String> untaken = Confirmation.close();
        Confirmation.Held held = OPEN_ARMS.isEmpty() ? null
                : Confirmation.held();
        synchronized (LOCK) {
            for (ObligationResult result : settled(sessionId, untaken,
                    held)) {
                if (!refusedAt.isEmpty()) {
                    results.add(ObligationResult.of(result.obligationId(),
                            Verdict.NOT_ADMITTED, result.sessionId(),
                            endedAtRefusal(result.detail()),
                            result.refutation()));
                } else if (!stalledAt.isEmpty()
                        && !FLIPPED.contains(result.obligationId())) {
                    results.add(ObligationResult.of(result.obligationId(),
                            Verdict.NOT_ADMITTED, result.sessionId(),
                            stalledAt + "; the replay ended there, after"
                                    + " another flip it was asked was"
                                    + " taken (until then: "
                                    + result.detail() + ")"));
                } else {
                    results.add(result);
                }
            }
        }
        return results;
    }

    private static String endedAtRefusal(String detail) {
        if (refusedAt.startsWith(REPLAY_NO_PROGRESS)) {
            return refusedAt + "; the replay ended there and published no"
                    + " session (until then: " + detail + ")";
        }
        return detail + (refusedAt.contains(detail)
                ? "; the replay ended at this refusal and published no session"
                : "; the replay ended at the refusal that decided every"
                        + " obligation it carried and published no session: "
                        + refusedAt);
    }

    private static List<ObligationResult> settled(String sessionId,
                                                  List<String> untaken,
                                                  Confirmation.Held held) {
        List<ObligationResult> results = new ArrayList<ObligationResult>();
        for (Obligation obligation : OBLIGATIONS) {
            String id = trimmed(obligation.obligationId());
            if (obligation.force()) {
                results.add(ForcedArms.verdict(id, sessionId));
            } else if (REFUSALS.containsKey(id)) {
                results.add(ObligationResult.of(id, Verdict.NOT_ADMITTED,
                        sessionId, REFUSALS.get(id)));
            } else if (FLIPPED.contains(id)) {
                String unstated = unstated(obligation);
                if (unstated.isEmpty()) unstated = inherited();
                if (unstated.isEmpty() && obligation.flips()
                        && !untaken.isEmpty()) {
                    unstated = PAIRING_UNTAKEN + ": the world this replay "
                            + "ran plants pairings it did not take: "
                            + String.join("; ", untaken);
                }
                results.add(unstated.isEmpty()
                        ? ObligationResult.of(id, Verdict.ADMITTED,
                                sessionId, obligation.pairing()
                                ? "the focused prefix reproduced and read "
                                + obligation.pairedReader() + " took version "
                                + obligation.pairedVersion() + " of its view"
                                : obligation.flips()
                                ? "the focused prefix reproduced and "
                                + trimmed(obligation.siteId()) + "#"
                                + obligation.ordinal() + " took "
                                + obligation.flippedOutcome()
                                : "the focused prefix reproduced and "
                                + "every root the model assigns was "
                                + "planted; no flip was owed")
                        : ObligationResult.of(id, Verdict.NOT_ADMITTED,
                                sessionId, unstated));
            } else if (trimmed(FOCUS.get(id)).isEmpty()) {
                results.add(ObligationResult.of(id, Verdict.NOT_ADMITTED,
                        sessionId, "the focus row states no "
                        + "focusedOccurrenceId, so the flip at "
                        + trimmed(obligation.siteId()) + "#"
                        + obligation.ordinal() + " is addressed at no "
                        + "occurrence of this replay"));
            } else {
                String detail = "occurrence " + trimmed(FOCUS.get(id))
                        + " never reached " + trimmed(obligation.siteId())
                        + "#" + obligation.ordinal() + " in this replay";
                List<String> unrefuted = new ArrayList<String>();
                WorldRefutation refutation = OPEN_ARMS.contains(id)
                        ? refuted(obligation, held, unrefuted) : null;
                String unrun = unrun(obligation);
                results.add(refutation == null
                        ? ObligationResult.of(id, Verdict.NOT_ADMITTED,
                        sessionId, !unrefuted.isEmpty()
                        ? ObligationResult.WORLD_UNREFUTED + ": " + detail
                        + "; its world is not refuted: "
                        + String.join("; ", unrefuted)
                        : unrun.isEmpty()
                        ? ObligationResult.WORLD_RAN + ": " + detail
                        + ", and the world it ran was the one asked"
                        : detail + "; its world did not run: " + unrun)
                        : ObligationResult.of(id, Verdict.NOT_ADMITTED,
                        sessionId, WORLD_REFUTED + ": " + detail + ", and the"
                        + " world it ran, faithfully, never entered it: "
                        + String.join("; ", refutation.conditions()),
                        refutation));
            }
        }
        return results;
    }

    static final String WORLD_REFUTED = "WORLD_REFUTED";

    private static String unrun(Obligation obligation) {
        return firstNonBlank(unstated(obligation), refusedAt, inherited(),
                unplantedLocked().isEmpty() ? ""
                        : "an assignment was left unplanted: "
                        + unplantedLocked());
    }

    private static WorldRefutation refuted(Obligation obligation,
                                           Confirmation.Held held,
                                           List<String> unrefuted) {
        String at = trimmed(FOCUS.get(trimmed(obligation.obligationId())));
        if (at.isEmpty() || ENTERED.contains(at)) return null;
        if (!workloadEnded) {
            unrefuted.add("(d) the workload did not end by itself");
        }
        String world = unrun(obligation);
        if (!world.isEmpty()) unrefuted.add("(a) " + world);
        if (held == null) {
            unrefuted.add("(b) the run's order holds could not be read");
        } else if (!held.gaveWay.isEmpty() || !held.misread.isEmpty()) {
            List<String> gave = new ArrayList<String>(held.gaveWay);
            gave.addAll(held.misread);
            unrefuted.add("(b) " + String.join("; ", gave));
        }
        Set<String> occurrence = new LinkedHashSet<String>();
        occurrence.add(at);
        if (task != null && task.focused() != null
                && task.focused().id().equals(at)) {
            occurrence.add(task.focused().anyDelivery().id());
        }
        List<String> holds = new ArrayList<String>();
        for (Map.Entry<String, Set<String>> hold : held == null
                ? new LinkedHashMap<String, Set<String>>().entrySet()
                : held.waiting.entrySet()) {
            for (String before : hold.getValue()) {
                int bar = before.indexOf('|');
                if (!occurrence.contains(bar < 0 ? before
                        : before.substring(0, bar))) {
                    unrefuted.add("(b) the hold of " + hold.getKey()
                            + " still waited at the end on " + before
                            + ", another occurrence than " + at);
                }
            }
            holds.add(hold.getKey() + " for " + hold.getValue());
        }
        long acted = FIRST_ACT.get();
        long departed = FIRST_DEPARTURE.get();
        if (acted == 0L) {
            unrefuted.add("(c) the world never acted in the window: no plant"
                    + " moved a value, no skew moved a clock, no answer moved"
                    + " an arrival and no hold waited");
        } else if (departed != 0L && departed < acted) {
            unrefuted.add("(c) slot " + firstDeparture + " was given up"
                    + " before the world first acted");
        }
        if (!unrefuted.isEmpty()) return null;
        List<String> conditions = new ArrayList<String>();
        conditions.add("(a) every assigned root and clock skew was minted at"
                + " its value and no prefix was abandoned");
        conditions.add("(b) no order hold gave way" + (holds.isEmpty() ? ""
                : ", and " + holds.size() + " still in force at the end"
                + " waited only on occurrence " + at + ": "
                + String.join(", ", holds)));
        conditions.add("(c) the recorded order held until the world first"
                + " acted" + (departed == 0L ? ": no slot was given up"
                : ": the first slot given up came after it"));
        conditions.add(endedAtClose
                ? "(d) the workload's test was over: its window closed"
                : "(d) the workload ended by itself"
                + (endedBy.isEmpty() ? ", its method returning"
                : ": " + endedBy + " thrown at " + endedAt
                + (endedInTest.isEmpty() ? "" : ", through " + endedInTest)));
        return WorldRefutation.of(conditions, endedBy, endedAt, endedInTest);
    }

    private static final Set<String> OPEN_ARMS = new LinkedHashSet<String>();

    private static final Set<String> ENTERED = ConcurrentHashMap.newKeySet();

    static void entered(OccurrenceAddress occurrence) {
        if (occurrence == null) return;
        ENTERED.add(occurrence.id());
        ENTERED.add(occurrence.anyDelivery().id());
    }

    private static final AtomicLong TICKS = new AtomicLong();
    private static final AtomicLong FIRST_ACT = new AtomicLong();
    private static final AtomicLong FIRST_DEPARTURE = new AtomicLong();

    static void worldActed() {
        if (!RecordingWindow.opened()) return;
        if (FIRST_ACT.get() == 0L) {
            FIRST_ACT.compareAndSet(0L, TICKS.incrementAndGet());
        }
    }

    static void departed(String slot) {
        if (FIRST_DEPARTURE.get() == 0L
                && FIRST_DEPARTURE.compareAndSet(0L, TICKS.incrementAndGet())) {
            firstDeparture = slot;
        }
    }

    private static volatile String firstDeparture = "";

    private static volatile boolean workloadEnded;
    private static volatile boolean endedAtClose;
    private static volatile String endedBy = "";
    private static volatile String endedAt = "";
    private static volatile String endedInTest = "";

    static void workloadEnded(Throwable failure, String testClass) {
        noteFailure(failure, testClass);
        workloadEnded = true;
    }

    private static void noteFailure(Throwable failure, String testClass) {
        if (failure != null) {
            String message = failure.getMessage() == null ? ""
                    : failure.getMessage().split("\\R", 2)[0];
            endedBy = failure.getClass().getName() + (message.isEmpty()
                    ? "" : ": " + (message.length() > 240
                    ? message.substring(0, 240) + "..." : message));
            StackTraceElement[] frames = failure.getStackTrace();
            endedAt = frames.length == 0 ? "" : frames[0].toString();
            for (StackTraceElement frame : frames) {
                if (frame.getClassName().equals(trimmed(testClass))) {
                    endedInTest = frame.toString();
                    break;
                }
            }
        }
    }

    static void windowClosed(Throwable failure, String testClass) {
        synchronized (LOCK) {
            if (workloadEnded || !refusedAt.isEmpty()
                    || !stalledAt.isEmpty()
                    || ConcolicResultPublisher.concluded()) {
                return;
            }
            noteFailure(failure, testClass);
            endedAtClose = true;
            workloadEnded = true;
        }
    }

    static long[] questionMoved() {
        load();
        synchronized (LOCK) {
            Set<String> focused = new LinkedHashSet<String>();
            for (String at : FOCUS.values()) focused.add(trimmed(at));
            focused.addAll(ROOT_MINTS);
            focused.addAll(INHERITED_OCCURRENCES);
            focused.retainAll(ENTERED);
            long inheritedTaken = 0L;
            for (Inherited flip : INHERITED) {
                if (flip.taken) inheritedTaken++;
            }
            return new long[] {focused.size(), FLIPPED.size(),
                    inheritedTaken, PLANTED.size(),
                    FIRST_ACT.get() == 0L ? 0L : 1L};
        }
    }

    private static String inherited() {
        for (Inherited flip : INHERITED) {
            if (!flip.refusal.isEmpty()) return flip.refusal;
        }
        for (Inherited flip : INHERITED) {
            if (!flip.taken) {
                return "this replay never reached the flip it INHERITED "
                        + "from the session its path was cut from: "
                        + flip.render();
            }
        }
        return "";
    }

    private static String unstated(Obligation obligation) {
        if (!unmatchedPrefix.isEmpty()) return unmatchedPrefix;
        if (!unsettledPublication.isEmpty()) return unsettledPublication;
        List<String> missing = new ArrayList<String>();
        if (obligation.rootAssignments() != null) {
            for (String rootId : obligation.rootAssignments().keySet()) {
                String id = trimmed(rootId);
                if (!id.isEmpty() && !MINTED.contains(id)) missing.add(id);
            }
        }
        for (String rootId : CLOCK_DELTAS.keySet()) {
            String id = trimmed(rootId);
            if (!id.isEmpty() && !MINTED.contains(id) && !missing.contains(id)) {
                missing.add(id);
            }
        }
        if (missing.isEmpty()) return "";
        return "this replay published no root mint row for " + missing
                + ", so its session states nothing about the value it ran"
                + " the root(s) the obligation moves at";
    }

    public static final String PLAN_PROPERTY = "causynth.concolic.task.plan";
    private static void loadPlanRows() {
        Path path = focusRow();
        if (path == null) return;
        handedAFocusRow = true;
        Task focusedTask = null;
        try {
            for (JsonObject row : RowCodec.readJsonl(path)) {
                if (!row.has("flip") || !row.has("taskId")) continue;
                String obligationId = optionalString(row, "obligationId");
                if (obligationId.isEmpty()) {
                    obligationId = optionalString(row, "taskId");
                }
                if (row.get("flip").isJsonNull() && row.has(FORCE)
                        && row.get(FORCE).getAsBoolean()) {
                    OBLIGATIONS.add(Obligation.forcing(obligationId,
                            optionalString(row, "taskId"),
                            optionalString(row, "pathId")));
                    FLIPPED.add(obligationId);
                    forcing = true;
                } else if (row.get("flip").isJsonNull()) {
                    OBLIGATIONS.add(Obligation.confirming(obligationId,
                            optionalString(row, "taskId"),
                            optionalString(row, "pathId"),
                            strings(row, "rootAssignments"),
                            strings(row, "answers"),
                            list(row, "unproducible")));
                    FLIPPED.add(obligationId);
                } else {
                    JsonObject flip = row.getAsJsonObject("flip");
                    if (!flip.has("ordinal") || !flip.has("outcome")) {
                        SHORTFALLS.add("the focus row for obligation "
                                + obligationId + " states a flip with no "
                                + (flip.has("ordinal") ? "outcome"
                                : "ordinal")
                                + ", so this replay enforces no flip for it"
                                + " and answers it with no verdict");
                        continue;
                    }
                    OBLIGATIONS.add(Obligation.of(obligationId,
                            optionalString(row, "taskId"),
                            optionalString(row, "pathId"),
                            optionalString(flip, "siteId"),
                            flip.get("ordinal").getAsInt(),
                            flip.get("outcome").getAsBoolean(),
                            strings(row, "rootAssignments"),
                            strings(row, "answers"),
                            list(row, "unproducible")));
                }
                FOCUS.put(obligationId,
                        optionalString(row, "focusedOccurrenceId"));
                if (row.has(OPEN_ARM) && !row.get(OPEN_ARM).isJsonNull()
                        && row.get(OPEN_ARM).getAsBoolean()) {
                    OPEN_ARMS.add(obligationId);
                }
                pairs |= !strings(row, "pairings").isEmpty();
                CLOCK_DELTAS.putAll(strings(row, "clockDeltas"));
                for (Map.Entry<String, String> mint
                        : strings(row, "rootMints").entrySet()) {
                    OccurrenceAddress at =
                            OccurrenceAddress.parse(mint.getValue());
                    if (at != null) ROOT_MINTS.add(at.id());
                }
                if (row.has("inheritedFlips")
                        && !row.get("inheritedFlips").isJsonNull()) {
                    for (JsonElement element
                            : row.getAsJsonArray("inheritedFlips")) {
                        if (!element.isJsonObject()) continue;
                        JsonObject carried = element.getAsJsonObject();
                        if (!carried.has("ordinal") || !carried.has("outcome")) {
                            SHORTFALLS.add("the focus row for obligation "
                                    + obligationId + " states an inherited "
                                    + "flip at "
                                    + optionalString(carried, "siteId")
                                    + " with no "
                                    + (carried.has("ordinal") ? "outcome"
                                    : "ordinal") + ", so this replay cannot"
                                    + " be held to the world it was cut"
                                    + " from");
                            continue;
                        }
                        if (Obligation.pairing(optionalString(carried,
                                "siteId"))) {
                            continue;
                        }
                        String at = optionalString(carried,
                                "focusedOccurrenceId");
                        INHERITED.add(new Inherited(at,
                                optionalString(carried, "siteId"),
                                carried.get("ordinal").getAsInt(),
                                carried.get("outcome").getAsBoolean(),
                                optionalString(carried, "obligationId")));
                        if (!at.isEmpty()) INHERITED_OCCURRENCES.add(at);
                    }
                }
                FOCUSED_TASKS.add(optionalString(row, "taskId"));
                if (declaredTarget.isEmpty()) {
                    declaredTarget = optionalString(row, "declaredTarget");
                }
                OccurrenceAddress focus = occurrence(row.get("focused"));
                if (focus != null && focusedTask == null) {
                    List<OccurrenceAddress> members =
                            new ArrayList<OccurrenceAddress>();
                    if (row.has("factor")) {
                        for (JsonElement member
                                : row.getAsJsonArray("factor")) {
                            OccurrenceAddress parsed = occurrence(member);
                            if (parsed != null) members.add(parsed);
                        }
                    }
                    String seed = optionalString(row, "seedSessionId");
                    if (!seed.isEmpty()) {
                        focusedTask = Task.of(optionalString(row, "taskId"),
                                focus, members, seed);
                    }
                }
            }
        } catch (RuntimeException | IOException unreadable) {
            SHORTFALLS.add("the focus row " + path + " could not be read"
                    + " whole (" + unreadable + "), so this session ran"
                    + " only the " + OBLIGATIONS.size() + " obligations it"
                    + " parsed before the fault");
        }
        if (!OBLIGATIONS.isEmpty() && task == null && focusedTask != null) {
            task = focusedTask;
        }
    }

    private static final List<String> SHORTFALLS = new ArrayList<String>();

    static List<String> shortfalls() {
        load();
        synchronized (LOCK) {
            return new ArrayList<String>(SHORTFALLS);
        }
    }

    private static boolean handedAFocusRow;

    public static boolean focusedSession() {
        load();
        synchronized (LOCK) {
            return handedAFocusRow;
        }
    }

    static boolean pairs() {
        load();
        synchronized (LOCK) {
            return pairs;
        }
    }

    private static boolean pairs;

    static boolean confirming() {
        load();
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                if (!obligation.flips() && !obligation.force()) return true;
            }
            return false;
        }
    }

    static final String FORCE = "force";

    private static boolean forcing;

    static boolean forcing() {
        load();
        synchronized (LOCK) {
            return forcing;
        }
    }

    static boolean decideForced(String divergence) {
        load();
        synchronized (LOCK) {
            return decide(divergence);
        }
    }

    public static List<String> obligationIds() {
        load();
        List<String> ids = new ArrayList<String>();
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                String id = trimmed(obligation.obligationId());
                if (!id.isEmpty() && !ids.contains(id)) ids.add(id);
            }
        }
        return ids;
    }

    public static void planted(String rootId, boolean moved) {
        load();
        String id = trimmed(rootId);
        if (id.isEmpty()) return;
        if (moved) worldActed();
        synchronized (LOCK) {
            PLANTED.add(id);
        }
    }

    static void answered(boolean moved) {
        if (moved) worldActed();
    }

    static void mintReached(String rootId) {
        String id = trimmed(rootId);
        if (id.isEmpty()) return;
        load();
        synchronized (LOCK) {
            REACHED.add(id);
        }
    }

    private static final Set<String> REACHED = new LinkedHashSet<String>();

    public static Map<String, String> unplantedAssignments() {
        load();
        synchronized (LOCK) {
            return unplantedLocked();
        }
    }

    private static Map<String, String> unplantedLocked() {
        Map<String, String> unplanted = new LinkedHashMap<String, String>();
        List<Map<String, String>> asked =
                new ArrayList<Map<String, String>>();
        for (Obligation obligation : OBLIGATIONS) {
            if (obligation.rootAssignments() != null) {
                asked.add(obligation.rootAssignments());
            }
        }
        asked.add(CLOCK_DELTAS);
        for (Map<String, String> roots : asked) {
            for (Map.Entry<String, String> assigned : roots.entrySet()) {
                String id = trimmed(assigned.getKey());
                if (id.isEmpty() || PLANTED.contains(id)) continue;
                if (!reachedLocked(id)) continue;
                unplanted.put(id, assigned.getValue());
            }
        }
        return unplanted;
    }

    private static final Set<String> PLANTED = new LinkedHashSet<String>();

    private static boolean reachedLocked(String id) {
        return REACHED.contains(id) || MINTED.contains(id);
    }

    public static final String OPEN_ARM = "openArm";

    private static Path focusRow() {
        return workerFile(ObligationDir.FOCUSED_TASK);
    }

    static Path workerFile(String name) {
        String worker = workerDir();
        if (!worker.isEmpty()) {
            Path inWorker = readable(Paths.get(worker).resolve(name));
            if (inWorker != null) return inWorker;
        }
        String plan = setting(PLAN_PROPERTY, "CAUSYNTH_CONCOLIC_TASK_PLAN");
        if (plan.isEmpty()) return null;
        Path beside = Paths.get(plan).getParent();
        return beside == null ? null : readable(beside.resolve(name));
    }

    static String workerDir() {
        return trimmed(System.getenv("CAUSYNTH_CONCOLIC_WORKER_DIR"));
    }

    private static Path readable(Path file) {
        return Files.isReadable(file) ? file : null;
    }

    private static void load() {
        synchronized (LOCK) {
            if (loaded) return;
            loaded = true;
            loadPlanRows();
        }
    }

    private static OccurrenceAddress occurrence(JsonElement element) {
        if (element == null || element.isJsonNull()) return null;
        if (element.isJsonPrimitive()) {
            return OccurrenceAddress.parse(element.getAsString());
        }
        return RowCodec.readOccurrence(element.getAsJsonObject());
    }

    private static Map<String, String> strings(JsonObject row,
                                               String member) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        if (!row.has(member) || row.get(member).isJsonNull()) return values;
        for (Map.Entry<String, JsonElement> entry
                : row.getAsJsonObject(member).entrySet()) {
            values.put(trimmed(entry.getKey()),
                    entry.getValue().getAsString());
        }
        return values;
    }

    private static List<String> list(JsonObject row, String member) {
        List<String> values = new ArrayList<String>();
        if (!row.has(member) || row.get(member).isJsonNull()) return values;
        for (JsonElement value : row.getAsJsonArray(member)) {
            values.add(trimmed(value.getAsString()));
        }
        return values;
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            loaded = false;
            handedAFocusRow = false;
            pairs = false;
            forcing = false;
            PLANTED.clear();
            MINTED.clear();
            REACHED.clear();
            unmatchedPrefix = "";
            unsettledPublication = "";
            refusedAt = "";
            stalledAt = "";
            ROOT_MINTS.clear();
            task = null;
            OBLIGATIONS.clear();
            CLOCK_DELTAS.clear();
            FOCUS.clear();
            REFUSALS.clear();
            FLIPPED.clear();
            FOCUSED_TASKS.clear();
            declaredTarget = "";
            FOCUSED_OCCURRENCES.clear();
            INHERITED.clear();
            INHERITED_OCCURRENCES.clear();
            SHORTFALLS.clear();
            OPEN_ARMS.clear();
            ENTERED.clear();
            FIRST_ACT.set(0L);
            FIRST_DEPARTURE.set(0L);
            firstDeparture = "";
            workloadEnded = false;
            endedAtClose = false;
            endedBy = "";
            endedAt = "";
            endedInTest = "";
        }
    }
}
