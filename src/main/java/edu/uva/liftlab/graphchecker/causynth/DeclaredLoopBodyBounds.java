package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.TreeSet;
import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;

/**
 * The {@code K_L} a campaign declares for the retained loops of its own
 * workload.
 *
 * <p>README section 5 makes {@code K_L} per loop: "every loop {@code L}
 * retained by an accepted model must declare {@code K_L}".  A declaration is
 * a statement about the workload, not a measurement of it - the planner has
 * no trip counts and must never acquire any - so it is read from campaign
 * configuration and keyed by the loop control site the planner already
 * computes.</p>
 *
 * <h2>The file</h2>
 *
 * <p>One JSONL row per declared loop, named by
 * {@code -D}{@value #SOURCE_PROPERTY} or
 * {@code $}{@value #SOURCE_ENVIRONMENT}, in the same idiom as the protocol
 * stub declarations beside it:</p>
 *
 * <pre>
 * {"loopSiteId": "&lt;a.B: void poll()&gt;#u7", "loopBodyBound": 32,
 *  "reason": "measured 20-29 body executions in the recorded pass"}
 * </pre>
 *
 * <p>{@code loopSiteId} is exactly one entry of the retained loop row's
 * {@link LoopBoundPolicy#LOOP_CONTROL_SITE_IDS} -
 * {@code &lt;method signature&gt;#u&lt;unitIndex&gt;} - so a declaration is
 * greppable against the artifact it applies to, in both directions.  The
 * {@code reason} travels beside the value because a bound with no stated
 * reason is a number nobody can re-derive.</p>
 *
 * <h2>Why a typo cannot be inherited silently</h2>
 *
 * <p>A key is not a hint.  A row naming a field this schema does not define,
 * or naming one loop twice, is refused when the file is read; a row whose
 * site no retained loop claims is refused by {@link #refuseUnclaimed()} once
 * planning has settled, naming {@link
 * LoopBoundPolicy#DECLARED_BOUND_SITE_UNDECLARED}.  Both matter because a
 * unit index moves when the workload is recompiled: without the refusal, a
 * stale key would leave its loop quietly inheriting {@link
 * LoopBoundPolicy#declaredDefault()} and the campaign would model a
 * prefix nobody asked for.  A value outside
 * {@code 1..}{@link LoopBoundPolicy#MAX_DECLARED_LOOP_BODY_ITERATIONS} is
 * refused where it is emitted, naming the key that stated it - mint time
 * refuses it anyway, and refusing here names the file instead of the row.</p>
 */
final class DeclaredLoopBodyBounds {
    /** System property naming the declarations file. */
    static final String SOURCE_PROPERTY = "causynth.loop.bounds";
    /** Environment variable naming the declarations file. */
    static final String SOURCE_ENVIRONMENT = "CAUSYNTH_LOOP_BOUNDS";
    /** Declaration field: the loop control site this bound is stated for. */
    static final String SITE_FIELD = LoopBoundPolicy.LOOP_SITE_ID;
    /** Declaration field: {@code K_L}. */
    static final String BOUND_FIELD =
            LoopBoundPolicy.LOOP_BODY_BOUND;
    /** Declaration field: why this workload holds that many body executions. */
    static final String REASON_FIELD = "reason";
    /** The greppable key one declaration is named by in every refusal. */
    static final String KEY_PREFIX = BOUND_FIELD + ".";
    /** A declaration row naming a field this schema does not define. */
    static final String FIELD_UNKNOWN = "BOUNDED_LOOP_BODY_BOUND_KEY_UNKNOWN";

    private static final Set<String> FIELDS = Collections.unmodifiableSet(
            new LinkedHashSet<String>(Arrays.asList(
                    SITE_FIELD, BOUND_FIELD, REASON_FIELD)));

    private final SortedMap<String, Declaration> bySite;
    private final Set<String> claimed = new LinkedHashSet<String>();

    private DeclaredLoopBodyBounds(SortedMap<String, Declaration> bySite) {
        this.bySite = bySite;
    }

    /** One declared loop, and where it was declared. */
    private static final class Declaration {
        private final String site;
        private final JsonElement value;
        private final String origin;

        private Declaration(String site, JsonElement value, String origin) {
            this.site = site;
            this.value = value;
            this.origin = origin;
        }

        /** The greppable key this declaration is named by. */
        private String key() {
            return KEY_PREFIX + site;
        }
    }

    /** A campaign that declares no bound: every retained loop inherits. */
    static DeclaredLoopBodyBounds none() {
        return new DeclaredLoopBodyBounds(
                new TreeMap<String, Declaration>());
    }

    /** The declarations this campaign's configuration names, if any. */
    static DeclaredLoopBodyBounds fromConfiguration() throws IOException {
        String configured = firstNonBlank(
                System.getProperty(SOURCE_PROPERTY),
                System.getenv(SOURCE_ENVIRONMENT));
        if (configured == null) {
            return none();
        }
        Path path = Paths.get(configured).toAbsolutePath().normalize();
        if (!Files.isRegularFile(path)) {
            throw new IOException("Loop body bound declarations not found: "
                    + path);
        }
        return read(path);
    }

    /** Reads one declarations file. */
    static DeclaredLoopBodyBounds read(Path path) throws IOException {
        SortedMap<String, Declaration> bySite =
                new TreeMap<String, Declaration>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                    continue;
                }
                String origin = path + ":" + lineNumber;
                Declaration declaration = parse(trimmed, origin);
                Declaration existing = bySite.get(declaration.site);
                if (existing != null) {
                    // One loop has one prefix, so one loop has one
                    // declaration: two rows for one site state two, and
                    // picking either would be this file choosing for the
                    // reader.
                    throw new IOException(
                            LoopBoundPolicy.LOOP_BODY_BOUND_DISAGREES
                                    + ": " + declaration.key()
                                    + " is declared at " + existing.origin
                                    + " and again at " + origin);
                }
                bySite.put(declaration.site, declaration);
            }
        }
        return new DeclaredLoopBodyBounds(bySite);
    }

    private static Declaration parse(String line, String origin)
            throws IOException {
        JsonObject row;
        try {
            JsonElement parsed = JsonParser.parseString(line);
            if (!parsed.isJsonObject()) {
                throw new IllegalArgumentException(
                        "declaration must be a JSON object");
            }
            row = parsed.getAsJsonObject();
        } catch (RuntimeException malformed) {
            throw new IOException("Invalid loop body bound declaration at "
                    + origin + ": " + malformed.getMessage(), malformed);
        }
        for (Map.Entry<String, JsonElement> field : row.entrySet()) {
            if (!FIELDS.contains(field.getKey())) {
                throw new IOException(FIELD_UNKNOWN + " at " + origin + ": "
                        + field.getKey() + "; a declaration states "
                        + FIELDS);
            }
        }
        JsonElement site = row.get(SITE_FIELD);
        JsonElement bound = row.get(BOUND_FIELD);
        if (site == null || !site.isJsonPrimitive()
                || site.getAsString().trim().isEmpty()) {
            throw new IOException(LoopBoundPolicy.DECLARED_BOUND_SITE_UNDECLARED
                    + " at " + origin + ": a declaration names the loop"
                    + " control site its bound is stated for");
        }
        if (bound == null || bound.isJsonNull()) {
            throw new IOException(FIELD_UNKNOWN + " at " + origin + ": "
                    + KEY_PREFIX + site.getAsString().trim()
                    + " states no " + BOUND_FIELD);
        }
        return new Declaration(site.getAsString().trim(), bound, origin);
    }

    /**
     * {@code K_L} for the retained loop one row's loop control sites name, or
     * {@code 0} when that loop declares none of its own. One loop has one
     * prefix, so every member site must declare the same bound; members that
     * state different bounds - or a member that declares one while another
     * inherits - are refused by name rather than resolved by picking either.
     * @throws IllegalArgumentException naming {@link
     *         LoopBoundPolicy#LOOP_BODY_BOUND_DISAGREES} or {@link
     *         LoopBoundPolicy#DECLARED_BOUND_OUT_OF_RANGE}, in both cases
     *         naming the configuration key that stated it
     */
    int bound(Collection<String> loopControlSiteIds) {
        if (bySite.isEmpty() || loopControlSiteIds == null
                || loopControlSiteIds.isEmpty()) {
            return 0;
        }
        // Sorted, so what one nest is refused or accepted for is a fact about
        // the CFG rather than about the order a reader walked its guards in.
        Set<String> sites = new TreeSet<String>(loopControlSiteIds);
        Declaration declared = null;
        int bound = 0;
        String undeclared = "";
        for (String site : sites) {
            Declaration row = bySite.get(site);
            if (row == null) {
                if (undeclared.isEmpty()) undeclared = site;
                continue;
            }
            claimed.add(site);
            int value = value(row);
            if (declared == null) {
                declared = row;
                bound = value;
            } else if (value != bound) {
                throw disagreement(sites, declared, bound, row.key(),
                        String.valueOf(value));
            }
        }
        if (declared == null) {
            return 0;
        }
        if (!undeclared.isEmpty()) {
            // An undeclared member is not silence: it inherits, and a nest
            // whose members hold two different prefixes has no one prefix.
            throw disagreement(sites, declared, bound, KEY_PREFIX + undeclared,
                    "absent, inheriting "
                            + LoopBoundPolicy.declaredDefault());
        }
        return bound;
    }

    /** Refuses every declaration no retained loop claimed. */
    void refuseUnclaimed() {
        List<String> unclaimed = new ArrayList<String>();
        for (Declaration declaration : bySite.values()) {
            if (!claimed.contains(declaration.site)) {
                unclaimed.add(declaration.key() + " (" + declaration.origin
                        + ")");
            }
        }
        if (unclaimed.isEmpty()) {
            return;
        }
        throw new IllegalStateException(
                LoopBoundPolicy.DECLARED_BOUND_SITE_UNDECLARED + ": "
                        + unclaimed + "; each key must name a loop control"
                        + " site of a retained loop, as "
                        + LoopBoundPolicy.LOOP_CONTROL_SITE_IDS
                        + " publishes it. A key that names no retained loop"
                        + " leaves its loop inheriting "
                        + LoopBoundPolicy.declaredDefault()
                        + " body executions, so it is refused rather than"
                        + " ignored");
    }

    private int value(Declaration declaration) {
        try {
            return LoopBoundPolicy.bodyBound(
                    declaration.value.isJsonPrimitive()
                            ? declaration.value.getAsString()
                            : declaration.value.toString());
        } catch (IllegalArgumentException refused) {
            throw new IllegalArgumentException(
                    LoopBoundPolicy.DECLARED_BOUND_OUT_OF_RANGE + ": "
                            + declaration.key() + "=" + declaration.value
                            + " declared at " + declaration.origin
                            + "; K_L is 1.."
                            + LoopBoundPolicy
                            .MAX_DECLARED_LOOP_BODY_ITERATIONS, refused);
        }
    }

    private IllegalArgumentException disagreement(
            Collection<String> sites, Declaration declared, int bound,
            String otherKey, String otherValue) {
        return new IllegalArgumentException(
                LoopBoundPolicy.LOOP_BODY_BOUND_DISAGREES + ": "
                        + declared.key() + "=" + bound + " (" + declared.origin
                        + ") and " + otherKey + "=" + otherValue
                        + " are members of one loop nest "
                        + LoopBoundPolicy.loopSiteId(sites)
                        + "; one loop has one prefix");
    }

}
