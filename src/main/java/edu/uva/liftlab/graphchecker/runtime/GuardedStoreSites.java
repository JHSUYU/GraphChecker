package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The static slice's control-dependence answer, as the VM's session table.
 *
 * <p>A concrete store is evidence only where the program text makes it
 * control-dependent on a branch a replay may flip (REPORT-VM22 VM24): the
 * VM starts a location's log at a concrete store only inside a method this
 * table names, and only once one of that method's guard branches has decided
 * symbolically in the current region frame.  The dependence itself is PLAN's
 * answer -- {@code static_scope_map.jsonl}, post-dominance in the enclosing
 * method's CFG (REPORT-CLOSURE-V2 SS1) -- so this class decides nothing: it
 * selects the {@code WRITE_SITE} rows that state a guard, groups them by the
 * method the VM spells an endpoint site with, and hands the result to
 * {@code System.installGuardedStoreSites}.</p>
 *
 * <p>Two spellings meet here and neither is rewritten. The store side is a
 * method: the map states its owner dotted ({@code a.b.C#m(desc)ret}) and the
 * VM asks with the owner internal ({@code a/b/C#m(desc)ret}), so only the
 * owner's dots become slashes. The guard side is a branch site id and is
 * passed verbatim -- {@code <owner: ret name(params)>#u<unit>}, the string
 * the woven {@code markConcolicBranch} call passes
 * (CausynthPipeline:2730 renders it with {@link
 * edu.uva.liftlab.graphchecker.plan.SiteId#of}) and the string the map's
 * {@code guards} member carries.</p>
 *
 * <p>Required since closure v2: the map is a PLAN artifact of the epoch the
 * replay belongs to, so a session that cannot read it is a broken campaign
 * and is refused by name -- an absent table is the pre-VM22 baseline, in
 * which no concrete store is ever evidence, and that is not something a
 * campaign may become by accident.</p>
 */
final class GuardedStoreSites {
    /** Where the epoch's static scope map is, as the campaign states it. */
    static final String PATH_PROPERTY = "causynth.static.scope.map";
    static final String PATH_ENVIRONMENT = "CAUSYNTH_STATIC_SCOPE_MAP";

    /** The VM's line format (sharedFieldVersions.cpp:557). */
    private static final char LINE = '\n';
    private static final char METHOD_END = '\t';
    private static final char GUARD_END = ',';

    private final Map<String, Set<String>> guardsByMethod;
    private final List<String> fragmentedGuards;

    private GuardedStoreSites(Map<String, Set<String>> guardsByMethod,
                              List<String> fragmentedGuards) {
        this.guardsByMethod = guardsByMethod;
        this.fragmentedGuards = fragmentedGuards;
    }

    /**
     * Installs the epoch's table, or names why this session has none.
     *
     * @return an empty string once the VM holds the table, otherwise a named
     * diagnostic the caller fails the session with
     */
    static String install(ConcolicVmBroker api) {
        String declared = declaredPath();
        if (declared.isEmpty()) {
            return "GUARDED_STORE_SITES_UNDECLARED: neither -D"
                    + PATH_PROPERTY + " nor $" + PATH_ENVIRONMENT
                    + " names this epoch's " + StaticScopeMap.FILE;
        }
        Path artifact = Paths.get(declared);
        if (!Files.isRegularFile(artifact)) {
            return "GUARDED_STORE_SITES_ARTIFACT_MISSING: " + artifact;
        }
        final GuardedStoreSites table;
        try {
            table = of(ArtifactIO.readJsonl(artifact));
        } catch (IOException | RuntimeException rejected) {
            return "GUARDED_STORE_SITES_ARTIFACT_REJECTED: " + artifact
                    + ": " + rejected.getMessage();
        }
        final int installed;
        try {
            installed = api.installGuardedStoreSites(table.text());
        } catch (Throwable failure) {
            return "GUARDED_STORE_SITES_INSTALL_FAILED: "
                    + failure.getClass().getName() + ": "
                    + failure.getMessage();
        }
        if (installed != table.methods()) {
            return "GUARDED_STORE_SITES_INSTALL_REFUSED: the VM kept "
                    + installed + " of the " + table.methods()
                    + " store methods the table names";
        }
        log("GUARDED_STORE_SITES|installed=" + installed + "|guardSites="
                + table.guardSites() + "|map=" + artifact);
        if (!table.fragmentedGuards.isEmpty()) {
            // Not silent: the VM's table splits a method's guard list on
            // ',' and a branch site id spells its method's parameters with
            // the same character, so these guard sites reach the VM as
            // fragments that match no decision and admit no store. The
            // effect is under-admission -- the pre-VM22 baseline for exactly
            // these methods -- never a store admitted without a decision.
            log("GUARDED_STORE_SITES_GUARD_FRAGMENTED|count="
                    + table.fragmentedGuards.size() + "|first="
                    + table.fragmentedGuards.get(0)
                    + "|reason=the VM's guard list is ','-separated and this"
                    + " site id contains ','");
        }
        return "";
    }

    /** The path the campaign states, property first, then environment. */
    static String declaredPath() {
        String property = value(System.getProperty(PATH_PROPERTY));
        return property.isEmpty()
                ? value(System.getenv(PATH_ENVIRONMENT)) : property;
    }

    /** The table one static scope map's rows state. */
    static GuardedStoreSites of(List<JsonObject> rows) {
        Map<String, Set<String>> guardsByMethod =
                new LinkedHashMap<String, Set<String>>();
        List<String> fragmented = new ArrayList<String>();
        for (JsonObject row : rows) {
            if (!StaticScopeMap.SITE_KIND.equals(member(row, "kind"))
                    || !StaticScopeMap.WRITE_SITE.equals(
                            member(row, "role"))) {
                continue;
            }
            List<String> guards = guards(row);
            if (guards.isEmpty()) continue;
            String method = internalMethod(member(row, "vmSite"),
                    member(row, SiteId.MEMBER));
            Set<String> stated = guardsByMethod.get(method);
            if (stated == null) {
                stated = new LinkedHashSet<String>();
                guardsByMethod.put(method, stated);
            }
            for (String guard : guards) {
                if (guard.indexOf(LINE) >= 0 || guard.indexOf(METHOD_END) >= 0) {
                    // A guard that breaks the line framing would make the
                    // VM read some other string as a store method, which is
                    // an admission this map never stated.
                    throw new IllegalStateException("guard site id contains "
                            + "the table's line framing: " + guard);
                }
                if (guard.indexOf(GUARD_END) >= 0
                        && !fragmented.contains(guard)) {
                    fragmented.add(guard);
                }
                stated.add(guard);
            }
        }
        return new GuardedStoreSites(guardsByMethod,
                Collections.unmodifiableList(fragmented));
    }

    /** One line per store method, in the order the map states them. */
    String text() {
        StringBuilder table = new StringBuilder();
        for (Map.Entry<String, Set<String>> entry
                : guardsByMethod.entrySet()) {
            table.append(entry.getKey()).append(METHOD_END);
            boolean first = true;
            for (String guard : entry.getValue()) {
                if (!first) table.append(GUARD_END);
                table.append(guard);
                first = false;
            }
            table.append(LINE);
        }
        return table.toString();
    }

    /** How many store methods the table names. */
    int methods() {
        return guardsByMethod.size();
    }

    /** How many distinct guard branch sites it names them by. */
    int guardSites() {
        Set<String> guards = new LinkedHashSet<String>();
        for (Set<String> stated : guardsByMethod.values()) {
            guards.addAll(stated);
        }
        return guards.size();
    }

    /**
     * One store method as the VM asks for it: the map's dotted owner with
     * the internal separator, and the name and descriptor unchanged.
     */
    static String internalMethod(String vmSite, String siteId) {
        String stated = value(vmSite);
        int owner = stated.indexOf('#');
        if (owner <= 0 || owner == stated.length() - 1) {
            throw new IllegalStateException("static scope map states a "
                    + "guarded write site with no vmSite method: " + siteId);
        }
        return stated.substring(0, owner).replace('.', '/')
                + stated.substring(owner);
    }

    private static List<String> guards(JsonObject row) {
        List<String> guards = new ArrayList<String>();
        JsonElement stated = row == null ? null : row.get("guards");
        if (stated != null && stated.isJsonArray()) {
            for (JsonElement guard : stated.getAsJsonArray()) {
                String site = value(guard.getAsString());
                if (!site.isEmpty()) guards.add(site);
            }
        }
        return guards;
    }

    private static String member(JsonObject row, String name) {
        JsonElement value = row == null ? null : row.get(name);
        return value == null || value.isJsonNull()
                ? "" : value(value.getAsString());
    }

    private static String value(String text) {
        return text == null ? "" : text.trim();
    }

    /** One line of the replay's session log, where the count is read. */
    private static void log(String detail) {
        try {
            System.err.println("CAUSYNTH-SESSION|" + detail);
        } catch (Throwable ignored) {
            // A session is not failed by an unwritable log.
        }
    }
}
