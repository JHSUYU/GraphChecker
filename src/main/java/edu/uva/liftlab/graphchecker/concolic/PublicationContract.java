package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * What the replay wave must have published for the stages after it to mean
 * anything, checked once, where the evidence is.
 *
 * <p>Every regression this pipeline had in one day was already visible in the
 * imported corpus and surfaced hours later as something else: a task that
 * published nothing became "the TARGET path worklist is not executable" after
 * five minutes of EXPLORE; a branch prefix the replay never decided became a
 * telemetry row nobody read until the same place; a write log the reader
 * refused became a formula with no root in it and an opaque
 * {@code CLOSURE_INCOMPLETE} at COMPOSE.  Each was a statement the corpus
 * could have made about itself at IMPORT.</p>
 *
 * <p>So this is a contract, not a heuristic.  It adds no information and
 * repairs nothing: it reads what the importer just wrote, names each way the
 * publication is short of what the plan asked for, and stops the campaign
 * there.  Every row it raises is BLOCKING, because each names a link of the
 * chain the later stages would have had to invent.</p>
 */
final class PublicationContract {

    /** A planned task the run left neither an activation nor a skip for. */
    static final String TASK_SILENT = "PUBLICATION_TASK_SILENT";
    /**
     * A kept task every run that was asked declined to answer.
     *
     * <p>A skip is a publication, and most skips say something about the
     * region: its causal anchor never ran before the workload ended, say.
     * One says something about the <em>run</em> instead -- "this run never
     * registered the epoch this task is addressed at" -- and when no other
     * run answered the task either, the region simply was not replayed.  It
     * looks like a published task and contributes nothing, which is how a
     * campaign came back FINAL_READY over a formula whose only
     * root-dependent region never ran.</p>
     */
    static final String TASK_ANSWERED_BY_NO_RUN =
            "PUBLICATION_TASK_ANSWERED_BY_NO_RUN";
    /** Skips that say which run was asked, not what the region did. */
    private static final String[] RUN_ADDRESSED_SKIPS = {
            "REGION_OCCURRENCE_ANCHOR_UNMATCHED",
            "ROOT_NEVER_EXECUTED",
    };
    /** A task whose activations never decided a site its goal addresses. */
    static final String BRANCH_PREFIX_UNPUBLISHED =
            "PUBLICATION_BRANCH_PREFIX_UNPUBLISHED";
    /** A target anchor whose own reach event states no predicate. */
    static final String TARGET_PREDICATE_UNSTATED =
            "PUBLICATION_TARGET_PREDICATE_UNSTATED";
    /** A write log the in-session reader cannot read a version out of. */
    static final String WRITE_LOG_INCOMPLETE =
            "PUBLICATION_WRITE_LOG_INCOMPLETE";

    /**
     * Row-level codes the importer already raises that are contract
     * violations in their own right.  They are counted into the same table so
     * that one summary answers "is this corpus usable", rather than a reader
     * having to know which of forty codes are fatal.
     */
    private static final String[] ADOPTED = {
            "BRANCH_REPLAY_MISMATCH",
            "WIRE_LEAVES_UNATTACHED",
            "REGION_TASK_NO_PUBLISHED_ACTIVATION",
            "SHARED_STATE_MALFORMED_ENVELOPE",
            "SHARED_STATE_MAP_STATE_IDENTITY_MISSING",
            "SHARED_STATE_MAP_STATE_IDENTITY_AMBIGUOUS",
            "LOCATION_NOT_NAMED_ACROSS_SESSIONS",
    };

    static final String KIND = "CONCOLIC_PUBLICATION_CONTRACT";

    private PublicationContract() {
    }

    /**
     * Every way this import is short of the plan, in plan order.
     *
     * @param tasks       the kept plan, by task id
     * @param summaries   the rows the importer admitted
     * @param diagnostics the rows it already refused, read for the codes
     *                    above and never re-derived
     */
    static List<JsonObject> check(Map<String, ExecutionTask> tasks,
                                  List<JsonObject> summaries,
                                  Collection<JsonObject> diagnostics) {
        List<JsonObject> rows = new ArrayList<>();
        Map<String, List<JsonObject>> byTask = summariesByTask(summaries);
        Set<String> named = namedTasks(diagnostics);
        for (Map.Entry<String, ExecutionTask> entry : tasks.entrySet()) {
            ExecutionTask task = entry.getValue();
            if (task == null || !task.executable()) continue;
            String taskId = entry.getKey();
            List<JsonObject> published = byTask.get(taskId);
            if ((published == null || published.isEmpty())
                    && !named.contains(taskId)) {
                rows.add(row(TASK_SILENT, taskId, "this kept task published"
                        + " neither an activation nor a skip, so its region"
                        + " states nothing at all; its anchor names "
                        + task.occurrenceId()));
                continue;
            }
            if ((published == null || published.isEmpty())
                    && onlyRunAddressedSkips(taskId, diagnostics)) {
                rows.add(row(TASK_ANSWERED_BY_NO_RUN, taskId,
                        "every run this task was offered to declined it for"
                                + " being addressed elsewhere, and none"
                                + " answered it, so its region was not"
                                + " replayed; its anchor names "
                                + task.occurrenceId()));
                continue;
            }
            // A region the replay skipped published a row and named itself
            // through that row's own diagnostic.  Its goal's prefix is
            // legitimately undecided -- nothing ran to decide it -- and the
            // skip is the statement, already counted under its own code.
            if (published == null || published.isEmpty()
                    || named.contains(taskId)
                    || !task.goalKind().capturesTargetReach()) {
                continue;
            }
            // Only a target-reach goal's branch list is a required path
            // prefix: the replay was asked to follow exactly it to the fatal
            // site.  A region-path goal's branches are the sites its region
            // contains, and an activation is free not to execute one.
            String missing = firstUndecidedSite(task, published);
            if (!missing.isEmpty()) {
                rows.add(row(BRANCH_PREFIX_UNPUBLISHED, taskId,
                        "no activation of this task decided "
                                + missing + ", which its goal "
                                + task.goalId() + " addresses, so the path"
                                + " the plan asked for was never replayed"));
            }
        }
        for (JsonObject summary : summaries) {
            JsonObject reach = object(summary,
                    PathObservation.TargetReachEvent.FIELD);
            if (reach.size() > 0
                    && optionalString(reach, "siteId").isEmpty()) {
                rows.add(row(TARGET_PREDICATE_UNSTATED,
                        optionalString(summary, "occurrenceId"),
                        "this activation published a target reach event that"
                                + " names no site, so the anchor has no"
                                + " predicate to compose"));
            }
            for (JsonElement element : array(summary, "alignmentGaps")) {
                if (!element.isJsonObject()) continue;
                JsonObject gap = element.getAsJsonObject();
                if (!"SHARED_STATE_MALFORMED_ENVELOPE".equals(
                        optionalString(gap, "reason"))) {
                    continue;
                }
                rows.add(row(WRITE_LOG_INCOMPLETE,
                        firstNonEmpty(optionalString(gap, "locationKey"),
                                optionalString(summary, "occurrenceId")),
                        "the write log this replay published for the location"
                                + " cannot be read back: "
                                + optionalString(gap, "detail")));
            }
        }
        for (JsonObject diagnostic : diagnostics) {
            String code = optionalString(diagnostic, "code");
            for (String adopted : ADOPTED) {
                if (!adopted.equals(code)) continue;
                rows.add(row(code, firstNonEmpty(
                        optionalString(diagnostic, "taskId"),
                        optionalString(diagnostic, "subject")),
                        optionalString(diagnostic, "detail")));
            }
        }
        return rows;
    }

    /** {@code code | count | first subject}, one table for the whole wave. */
    static List<String> table(List<JsonObject> rows) {
        Map<String, int[]> counts = new LinkedHashMap<>();
        Map<String, String> first = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            String code = optionalString(row, "code");
            counts.computeIfAbsent(code, ignored -> new int[1])[0]++;
            first.putIfAbsent(code, optionalString(row, "subject"));
        }
        List<String> lines = new ArrayList<>();
        lines.add(String.format("%-44s %5s  %s",
                "code", "count", "first subject"));
        for (Map.Entry<String, int[]> entry : counts.entrySet()) {
            lines.add(String.format("%-44s %5d  %s", entry.getKey(),
                    entry.getValue()[0], first.get(entry.getKey())));
        }
        return lines;
    }

    private static String firstUndecidedSite(
            ExecutionTask task, List<JsonObject> published) {
        Set<String> decided = new LinkedHashSet<>();
        for (JsonObject summary : published) {
            for (JsonElement element : array(summary, "branchMappings")) {
                if (!element.isJsonObject()) continue;
                JsonObject mapping = element.getAsJsonObject();
                addSite(decided, object(object(mapping,
                        "concreteObservation"), "site"));
                addSite(decided, object(object(mapping, "witness"), "site"));
            }
        }
        for (JsonElement element : task.branches()) {
            if (!element.isJsonObject()) continue;
            String site = optionalString(element.getAsJsonObject(), "siteId");
            if (!site.isEmpty() && !decided.contains(site)) return site;
        }
        return "";
    }

    private static void addSite(Set<String> decided, JsonObject site) {
        String siteId = optionalString(site, "siteId");
        if (!siteId.isEmpty()) decided.add(siteId);
    }

    /**
     * Whether every diagnostic naming this task says which run was asked.
     *
     * <p>A task with a real skip -- an anchor that never ran, a region the
     * plan named and the program did not enter -- has been answered.  A task
     * whose only rows say "not this run" has not.</p>
     */
    private static boolean onlyRunAddressedSkips(
            String taskId, Collection<JsonObject> diagnostics) {
        boolean any = false;
        for (JsonObject diagnostic : diagnostics) {
            if (!taskId.equals(optionalString(diagnostic, "taskId"))) continue;
            String code = optionalString(diagnostic, "code");
            boolean addressed = false;
            for (String skip : RUN_ADDRESSED_SKIPS) {
                addressed |= skip.equals(code);
            }
            if (!addressed) return false;
            any = true;
        }
        return any;
    }

    private static Map<String, List<JsonObject>> summariesByTask(
            List<JsonObject> summaries) {
        Map<String, List<JsonObject>> byTask = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            byTask.computeIfAbsent(optionalString(summary, "taskId"),
                    ignored -> new ArrayList<>()).add(summary);
        }
        return byTask;
    }

    /** Tasks the importer already named, whatever it named them for. */
    private static Set<String> namedTasks(
            Collection<JsonObject> diagnostics) {
        Set<String> named = new LinkedHashSet<>();
        for (JsonObject diagnostic : diagnostics) {
            String taskId = optionalString(diagnostic, "taskId");
            if (!taskId.isEmpty()) named.add(taskId);
        }
        return named;
    }

    private static JsonObject row(String code, String subject,
                                  String detail) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", KIND);
        row.addProperty("stage", "IMPORT");
        row.addProperty("source", "PUBLICATION_CONTRACT");
        row.addProperty("code", code);
        row.addProperty("subject", subject);
        row.addProperty("detail", detail);
        return row;
    }

    private static String firstNonEmpty(String value, String fallback) {
        return value == null || value.isEmpty() ? fallback : value;
    }
}
