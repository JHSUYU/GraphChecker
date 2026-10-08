package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * THE FORCING TABLE of the declared throw (PIPELINE §2, §5): for each branch
 * between the target region's entry and the throw, the arm that leads to the
 * throw, keyed by the branch site id the woven decision marker and every
 * DecisionRow name.  SEED states it on the TARGET_SITE row ({@code force}),
 * PLAN copies it onto the declared task's {@code targetBranch.force}, and a
 * forced replay ({@code runtime.ForcedArms}) forces those arms at the
 * declared occurrence.
 *
 * <p>The arms: each of the throw's guards at its fatal arm, each guard of
 * the {@code chain} at its arm toward the guard it controls, and the helper
 * branch arms that decide a guard on a helper's constant return
 * ({@code guardDeciders}): the arm whose verdict is the guard's wanted
 * arm, else the OPEN arm (it runs on to a value no constant states, where
 * the fatal may lie), nested deciders alike, each with {@code via}, the
 * method that calls its helper (a decider is forced only in a call from
 * there).  A switch guard of the throw's method is forced to the one case
 * from which the throw is reachable ({@code Guards#switchCase}); a fault
 * call, which no branch decides, is not forced.</p>
 */
public final class ForcingTable {
    /** An if's arm: {@link Arm#value} 1 jumps, 0 falls through. */
    public static final int ARM = 1;
    /** A switch's case: {@link Arm#value} is its key. */
    public static final int CASE = 2;
    /** A switch's default. */
    public static final int DEFAULT = 3;

    private ForcingTable() {
    }

    /** One branch to force, as the VM is asked it
     *  ({@code System.forceNextConcolicBranch(kind, value)}). */
    public static final class Arm {
        public final String siteId;
        public final int kind;
        public final int value;
        /** The method a decider's helper must be called from, or "". */
        public final String via;

        Arm(String siteId, int kind, int value, String via) {
            this.siteId = siteId;
            this.kind = kind;
            this.value = value;
            this.via = via == null ? "" : via;
        }

        JsonObject toJson() {
            JsonObject json = new JsonObject();
            json.addProperty("siteId", siteId);
            if (kind == ARM) json.addProperty("arm", value != 0);
            if (kind == CASE) json.addProperty("case", value);
            if (kind == DEFAULT) json.addProperty("default", true);
            if (!via.isEmpty()) json.addProperty("via", via);
            return json;
        }

        @Override
        public String toString() {
            return siteId + (kind == ARM ? "=" + (value != 0)
                    : kind == CASE ? " case " + value : " default")
                    + (via.isEmpty() ? "" : " via " + via);
        }
    }

    /** SEED: the table of one TARGET_SITE, from its guards, chain and
     *  deciders; a site named twice keeps its first arm. */
    public static JsonArray of(StaticScopeMap.Site target,
                               StaticScopeMap.Guards guards) {
        Map<String, Arm> table = new LinkedHashMap<String, Arm>();
        for (int index = 0; index < target.guards.size(); index++) {
            String site = target.guards.get(index);
            Boolean arm = target.guardOutcomes.size() > index
                    ? target.guardOutcomes.get(index) : null;
            branch(table, site, arm, target.siteId, guards);
            List<StaticScopeMap.Guard> deciders =
                    target.guardDeciders.get(site);
            if (arm != null && deciders != null) {
                deciders(table, deciders, arm, SiteId.methodOf(site));
            }
        }
        for (StaticScopeMap.Guard guard : target.chain) {
            branch(table, guard.siteId(), guard.outcome(), target.siteId,
                    guards);
            if (guard.outcome() != null) {
                deciders(table, guard.deciders(), guard.outcome(),
                        SiteId.methodOf(guard.siteId()));
            }
        }
        JsonArray json = new JsonArray();
        for (Arm forced : table.values()) json.add(forced.toJson());
        return json;
    }

    /** One guard: an if at its arm; a switch at the case the throw is
     *  reachable from. */
    private static void branch(Map<String, Arm> table, String site,
                               Boolean arm, String throwSite,
                               StaticScopeMap.Guards guards) {
        if (table.containsKey(site)) return;
        if (arm != null) {
            table.put(site, new Arm(site, ARM, arm ? 1 : 0, ""));
            return;
        }
        String reaching = guards == null ? null
                : guards.switchCase(site, throwSite);
        if (reaching == null) return;
        table.put(site, StaticScopeMap.Guards.DEFAULT_CASE.equals(reaching)
                ? new Arm(site, DEFAULT, 0, "")
                : new Arm(site, CASE, Integer.parseInt(reaching), ""));
    }

    /**
     * The decider arms of one guard that make it take {@code wanted}: per
     * decider site the arm whose verdict is {@code wanted}, else its open
     * arm; the deciders of the arm chosen, in turn, at that arm.
     */
    private static void deciders(Map<String, Arm> table,
                                 List<StaticScopeMap.Guard> deciders,
                                 boolean wanted, String via) {
        Map<String, StaticScopeMap.Guard> chosen =
                new LinkedHashMap<String, StaticScopeMap.Guard>();
        for (StaticScopeMap.Guard decider : deciders) {
            if (decider.outcome() == null) continue;
            StaticScopeMap.Guard held = chosen.get(decider.siteId());
            boolean fatal = decider.verdict() != null
                    && decider.verdict().booleanValue() == wanted;
            boolean heldFatal = held != null && held.verdict() != null
                    && held.verdict().booleanValue() == wanted;
            if (fatal && !heldFatal
                    || held == null && decider.verdict() == null) {
                chosen.put(decider.siteId(), decider);
            }
        }
        for (StaticScopeMap.Guard decider : chosen.values()) {
            if (table.containsKey(decider.siteId())) continue;
            table.put(decider.siteId(), new Arm(decider.siteId(), ARM,
                    decider.outcome() ? 1 : 0, via));
            deciders(table, decider.deciders(), decider.outcome(),
                    SiteId.methodOf(decider.siteId()));
        }
    }

    /** A table as {@link #of} wrote it, by site; a row it cannot read is
     *  none. */
    public static Map<String, Arm> read(JsonElement json) {
        Map<String, Arm> table = new LinkedHashMap<String, Arm>();
        if (json == null || !json.isJsonArray()) return table;
        for (JsonElement element : json.getAsJsonArray()) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String site = optionalString(row, "siteId");
            if (site.isEmpty() || table.containsKey(site)) continue;
            String via = optionalString(row, "via");
            if (row.has("arm")) {
                table.put(site, new Arm(site, ARM,
                        row.get("arm").getAsBoolean() ? 1 : 0, via));
            } else if (row.has("case")) {
                table.put(site, new Arm(site, CASE,
                        row.get("case").getAsInt(), via));
            } else if (row.has("default")) {
                table.put(site, new Arm(site, DEFAULT, 0, via));
            }
        }
        return Collections.unmodifiableMap(table);
    }

    /** Every row of several tables, a site named twice kept once. */
    public static JsonArray union(List<JsonArray> tables) {
        Map<String, JsonElement> rows = new LinkedHashMap<String, JsonElement>();
        for (JsonArray table : tables) {
            for (JsonElement row : table) {
                if (!row.isJsonObject()) continue;
                rows.putIfAbsent(optionalString(row.getAsJsonObject(),
                        "siteId"), row);
            }
        }
        JsonArray json = new JsonArray();
        for (JsonElement row : rows.values()) json.add(row.deepCopy());
        return json;
    }
}
