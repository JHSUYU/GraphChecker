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
 * PLAN's control-dependence answer ({@code static_scope_map.jsonl},
 * REPORT-CLOSURE-V2 SS1) installed as the VM's session table: the VM logs a
 * concrete store only inside a method named here, once one of its guard
 * branches decided symbolically (REPORT-VM22 VM24).  Decides nothing itself.
 *
 * <p>Store methods go to the VM with the owner's dots made slashes; guard
 * site ids ({@link edu.uva.liftlab.graphchecker.plan.SiteId#of}) go
 * verbatim, and contain commas, hence tab-separated fields (VM25).</p>
 *
 * <p>Required: a missing table would silently mean no concrete store is
 * ever evidence, so it is refused by name.</p>
 */
final class GuardedStoreSites {
    /** Names this epoch's scope map; {@link ClockLoops} reads it too. */
    static final String PATH_ENVIRONMENT = "CAUSYNTH_STATIC_SCOPE_MAP";

    /** VM25: {@code line ::= methodKey ( '\t' guardSite )*}. */
    private static final char LINE = '\n';
    private static final char FIELD = '\t';

    private final Map<String, Set<String>> guardsByMethod;

    private GuardedStoreSites(Map<String, Set<String>> guardsByMethod) {
        this.guardsByMethod = guardsByMethod;
    }

    /**
     * Installs the epoch's table.
     *
     * @return "" once installed, else the diagnostic the session fails with
     */
    static String install(ConcolicVmBroker api) {
        String declared = value(System.getenv(PATH_ENVIRONMENT));
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
        // Every method here has a guard, so the VM must keep them all.
        if (installed != table.methods()) {
            return "GUARDED_STORE_SITES_INSTALL_REFUSED: the VM kept "
                    + installed + " of the " + table.methods()
                    + " guarded store methods the table names";
        }
        log("GUARDED_STORE_SITES|installed=" + installed + "|guardSites="
                + table.guardSites() + "|map=" + artifact);
        return "";
    }

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
                    // Would make the VM read another string as a method.
                    throw new IllegalStateException("guard site id contains "
                            + "the table's field framing: " + guard);
                }
                stated.add(guard);
            }
        }
        return new GuardedStoreSites(guardsByMethod);
    }

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

    int methods() {
        return guardsByMethod.size();
    }

    int guardSites() {
        Set<String> guards = new LinkedHashSet<String>();
        for (Set<String> stated : guardsByMethod.values()) {
            guards.addAll(stated);
        }
        return guards.size();
    }

    /** One store method as the VM asks for it: owner in internal form. */
    private static String internalMethod(String vmSite, String siteId) {
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

    private static void log(String detail) {
        try {
            System.err.println("CAUSYNTH-SESSION|" + detail);
        } catch (Throwable ignored) {
        }
    }
}
