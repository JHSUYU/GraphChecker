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
 * {@code guards} member carries.  Its parameter list contains commas, which
 * is why a line's guard sites are tab-separated fields (VM25) and not a
 * comma list: a comma list fragmented 15 of 17960's 27 guard ids and every
 * fragment matched nothing.</p>
 *
 * <p>Required since closure v2: the map is a PLAN artifact of the epoch the
 * replay belongs to, so a session that cannot read it is a broken campaign
 * and is refused by name -- an absent table is the pre-VM22 baseline, in
 * which no concrete store is ever evidence, and that is not something a
 * campaign may become by accident.</p>
 */
final class GuardedStoreSites {
    /** Where the epoch's static scope map is, as the campaign states it. */
    static final String PATH_ENVIRONMENT = "CAUSYNTH_STATIC_SCOPE_MAP";

    /**
     * The VM's grammar (VM25):
     * {@code line ::= methodKey ( '\t' guardSite )*}, lines split on
     * {@code '\n'} and fields on {@code '\t'} and on nothing else -- so a
     * guard site id carries its parameter list's commas whole.
     */
    private static final char LINE = '\n';
    private static final char FIELD = '\t';

    private final Map<String, Set<String>> guardsByMethod;

    private GuardedStoreSites(Map<String, Set<String>> guardsByMethod) {
        this.guardsByMethod = guardsByMethod;
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
            return "GUARDED_STORE_SITES_UNDECLARED: $" + PATH_ENVIRONMENT
                    + " does not name this epoch's " + StaticScopeMap.FILE;
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
        // The VM drops a method with no guard site, and every method this
        // table names has one, so the count it answers is the table's own.
        if (installed != table.methods()) {
            return "GUARDED_STORE_SITES_INSTALL_REFUSED: the VM kept "
                    + installed + " of the " + table.methods()
                    + " guarded store methods the table names";
        }
        log("GUARDED_STORE_SITES|installed=" + installed + "|guardSites="
                + table.guardSites() + "|map=" + artifact);
        return "";
    }

    /** The path the campaign states, in the one spelling it sets. */
    static String declaredPath() {
        return value(System.getenv(PATH_ENVIRONMENT));
    }

    /** The table one static scope map's rows state. */
    static GuardedStoreSites of(List<JsonObject> rows) {
        Map<String, Set<String>> guardsByMethod =
                new LinkedHashMap<String, Set<String>>();
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
                if (guard.indexOf(LINE) >= 0 || guard.indexOf(FIELD) >= 0) {
                    // A guard that breaks the framing would make the VM read
                    // some other string as a store method, which is an
                    // admission this map never stated.
                    throw new IllegalStateException("guard site id contains "
                            + "the table's field framing: " + guard);
                }
                stated.add(guard);
            }
        }
        return new GuardedStoreSites(guardsByMethod);
    }

    /** One line per store method, in the order the map states them. */
    String text() {
        StringBuilder table = new StringBuilder();
        for (Map.Entry<String, Set<String>> entry
                : guardsByMethod.entrySet()) {
            table.append(entry.getKey());
            for (String guard : entry.getValue()) {
                table.append(FIELD).append(guard);
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
