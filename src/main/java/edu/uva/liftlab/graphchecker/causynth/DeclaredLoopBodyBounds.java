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
import static edu.uva.liftlab.graphchecker.smt.JsonFields.setting;

/**
 * The per-loop {@code K_L} (PIPELINE §2), declared (never measured: the
 * planner has no trip counts) in a JSONL file named by {@code
 * -D}{@value #SOURCE_PROPERTY} or {@code $}{@value #SOURCE_ENVIRONMENT}:
 *
 * <pre>
 * {"loopSiteId": "&lt;a.B: void poll()&gt;#u7", "loopBodyBound": 32,
 *  "reason": "measured 20-29 body executions in the recorded pass"}
 * </pre>
 *
 * <p>{@code loopSiteId} is one entry of {@link
 * LoopBoundPolicy#LOOP_CONTROL_SITE_IDS}.  A key is not a hint: an unknown
 * field, a duplicate site, a site of an analysed method no retained loop
 * claims ({@link #refuseUnclaimed(Set)}) and a value outside {@code 1..}{@link
 * LoopBoundPolicy#MAX_DECLARED_LOOP_BODY_ITERATIONS} are all refused, since a
 * stale unit index would otherwise silently inherit {@link
 * LoopBoundPolicy#declaredDefault()}.</p>
 */
final class DeclaredLoopBodyBounds {
    static final String SOURCE_PROPERTY = "causynth.loop.bounds";
    static final String SOURCE_ENVIRONMENT = "CAUSYNTH_LOOP_BOUNDS";
    static final String SITE_FIELD = LoopBoundPolicy.LOOP_SITE_ID;
    static final String BOUND_FIELD =
            LoopBoundPolicy.LOOP_BODY_BOUND;
    static final String REASON_FIELD = "reason";
    /** The greppable key one declaration is named by in every refusal. */
    static final String KEY_PREFIX = BOUND_FIELD + ".";
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

        private String key() {
            return KEY_PREFIX + site;
        }
    }

    /** A campaign that declares no bound: every retained loop inherits. */
    private static DeclaredLoopBodyBounds none() {
        return new DeclaredLoopBodyBounds(
                new TreeMap<String, Declaration>());
    }

    /** The declarations this campaign's configuration names, if any. */
    static DeclaredLoopBodyBounds fromConfiguration() throws IOException {
        String configured = setting(SOURCE_PROPERTY, SOURCE_ENVIRONMENT);
        if (configured.isEmpty()) {
            return none();
        }
        Path path = Paths.get(configured).toAbsolutePath().normalize();
        if (!Files.isRegularFile(path)) {
            throw new IOException("Loop body bound declarations not found: "
                    + path);
        }
        return read(path);
    }

    private static DeclaredLoopBodyBounds read(Path path)
            throws IOException {
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
     * {@code K_L} for the loop these control sites name, or {@code 0} when
     * undeclared.  One loop has one prefix: members declaring different
     * bounds, or one declaring while another inherits, are refused.
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
        // Sorted: the verdict must not depend on guard walk order.
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
            // An undeclared member inherits: two prefixes in one nest.
            throw disagreement(sites, declared, bound, KEY_PREFIX + undeclared,
                    "absent, inheriting "
                            + LoopBoundPolicy.declaredDefault());
        }
        return bound;
    }

    /**
     * Refuses every declaration of a loop in {@code analysed} that no retained
     * loop claimed: a stale or misspelled key of a method the slice holds.  A
     * declaration of a method the slice never reached is a system-wide row
     * this campaign has no loop for (one experiment's declarations serve
     * every check of it), and binds nothing here.
     */
    void refuseUnclaimed(Set<String> analysed) {
        List<String> unclaimed = new ArrayList<String>();
        for (Declaration declaration : bySite.values()) {
            int unit = declaration.site.lastIndexOf('#');
            String method = unit < 0 ? declaration.site
                    : declaration.site.substring(0, unit);
            if (analysed.contains(method)
                    && !claimed.contains(declaration.site)) {
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
