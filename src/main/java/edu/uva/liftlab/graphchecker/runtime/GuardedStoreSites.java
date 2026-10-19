package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

final class GuardedStoreSites {
    static final String PATH_ENVIRONMENT = "CAUSYNTH_STATIC_SCOPE_MAP";

    private static final char LINE = '\n';
    private static final char FIELD = '\t';

    private final Map<String, Map<String, Set<String>>> guardsBySite;

    private GuardedStoreSites(
            Map<String, Map<String, Set<String>>> guardsBySite) {
        this.guardsBySite = guardsBySite;
    }

    static String install(ConcolicVmBroker api) {
        String declared = trimmed(System.getenv(PATH_ENVIRONMENT));
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
            List<JsonObject> rows = ArtifactIO.readJsonl(artifact);
            table = of(rows);
            ClockLoops.install(rows);
            RowPublication.installReadSites(rows);
            MessageCodec.install(rows);
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
        if (installed != table.sites()) {
            return "GUARDED_STORE_SITES_INSTALL_REFUSED: the VM kept "
                    + installed + " of the " + table.sites()
                    + " guarded store sites the table names";
        }
        log("GUARDED_STORE_SITES|installed=" + installed + "|guardSites="
                + table.guardSites() + "|map=" + artifact);
        return "";
    }

    static GuardedStoreSites of(List<JsonObject> rows) {
        Map<String, Map<String, Set<String>>> guardsBySite =
                new LinkedHashMap<String, Map<String, Set<String>>>();
        for (JsonObject row : rows) {
            if (!StaticScopeMap.SITE_KIND.equals(member(row, "kind"))
                    || !StaticScopeMap.WRITE_SITE.equals(
                            member(row, "role"))
                    || StaticScopeMap.constructionOnly(row)) {
                continue;
            }
            List<String> guards = guards(row);
            if (guards.isEmpty()) continue;
            String siteId = member(row, SiteId.MEMBER);
            String method = internalMethod(member(row, "vmSite"), siteId);
            String store = store(row, siteId);
            Set<String> stated = guardsBySite
                    .computeIfAbsent(method,
                            key -> new LinkedHashMap<String, Set<String>>())
                    .computeIfAbsent(store,
                            key -> new LinkedHashSet<String>());
            for (String guard : guards) {
                if (guard.indexOf(LINE) >= 0 || guard.indexOf(FIELD) >= 0) {
                    throw new IllegalStateException("guard site id contains "
                            + "the table's field framing: " + guard);
                }
                stated.add(guard);
            }
        }
        return new GuardedStoreSites(guardsBySite);
    }

    String text() {
        StringBuilder table = new StringBuilder();
        for (Map.Entry<String, Map<String, Set<String>>> method
                : guardsBySite.entrySet()) {
            for (Map.Entry<String, Set<String>> site
                    : method.getValue().entrySet()) {
                table.append(method.getKey()).append(FIELD)
                        .append(site.getKey());
                for (String guard : site.getValue()) {
                    table.append(FIELD).append(guard);
                }
                table.append(LINE);
            }
        }
        return table.toString();
    }

    int sites() {
        int sites = 0;
        for (Map<String, Set<String>> stores : guardsBySite.values()) {
            sites += stores.size();
        }
        return sites;
    }

    int guardSites() {
        Set<String> guards = new LinkedHashSet<String>();
        for (Map<String, Set<String>> stores : guardsBySite.values()) {
            for (Set<String> stated : stores.values()) guards.addAll(stated);
        }
        return guards.size();
    }

    private static String store(JsonObject row, String siteId) {
        String callee = member(row, "declaredCallee");
        if (!callee.isEmpty()) {
            int open = callee.indexOf('(');
            int space = open < 0 ? -1 : callee.lastIndexOf(' ', open);
            if (space < 0) {
                throw new IllegalStateException("static scope map states a "
                        + "guarded write site whose callee is no method: "
                        + siteId + " " + callee);
            }
            return "CALL " + callee.substring(space + 1, open);
        }
        FieldPathSpec.DeclaredField field =
                FieldPathSpec.declaredField(member(row, "cell"));
        if (field == null) {
            throw new IllegalStateException("static scope map states a "
                    + "guarded write site with no field: " + siteId);
        }
        return "FIELD " + field.owner().replace('.', '/') + "."
                + field.name();
    }

    private static String internalMethod(String vmSite, String siteId) {
        String stated = trimmed(vmSite);
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
                String site = trimmed(guard.getAsString());
                if (!site.isEmpty()) guards.add(site);
            }
        }
        return guards;
    }

    private static String member(JsonObject row, String name) {
        JsonElement value = row == null ? null : row.get(name);
        return value == null || value.isJsonNull()
                ? "" : trimmed(value.getAsString());
    }

    private static void log(String detail) {
        try {
            EngineConsole.println("CAUSYNTH-SESSION|" + detail);
        } catch (Throwable ignored) {
        }
    }
}
