package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class ForcingTable {
    private ForcingTable() {
    }

    public static final class Arm {
        public final String siteId;
        public final boolean arm;
        public final String via;
        public final boolean passable;

        Arm(String siteId, boolean arm, String via, boolean passable) {
            this.siteId = siteId;
            this.arm = arm;
            this.via = via == null ? "" : via;
            this.passable = passable;
        }

        JsonObject toJson() {
            JsonObject json = new JsonObject();
            json.addProperty("siteId", siteId);
            json.addProperty("arm", arm);
            if (!via.isEmpty()) json.addProperty("via", via);
            if (passable) json.addProperty(PASSABLE, true);
            return json;
        }

        @Override
        public String toString() {
            return siteId + "=" + arm + (via.isEmpty() ? "" : " via " + via)
                    + (passable ? " passable" : "");
        }
    }

    private static final String PASSABLE = "passable";

    public static JsonArray of(StaticScopeMap.Site target,
                               Set<String> passable) {
        Map<String, Arm> table = new LinkedHashMap<String, Arm>();
        for (int index = 0; index < target.guards.size(); index++) {
            String site = target.guards.get(index);
            Boolean arm = target.guardOutcomes.size() > index
                    ? target.guardOutcomes.get(index) : null;
            branch(table, site, arm, passable);
            List<StaticScopeMap.Guard> deciders =
                    target.guardDeciders.get(site);
            if (arm != null && deciders != null) {
                deciders(table, deciders, arm);
            }
        }
        for (StaticScopeMap.Guard guard : target.chain) {
            branch(table, guard.siteId(), guard.outcome(), passable);
            if (guard.outcome() != null) {
                deciders(table, guard.deciders(), guard.outcome());
            }
        }
        JsonArray json = new JsonArray();
        for (Arm forced : table.values()) json.add(forced.toJson());
        return json;
    }

    private static void branch(Map<String, Arm> table, String site,
                               Boolean arm, Set<String> passable) {
        if (arm != null && !table.containsKey(site)) {
            table.put(site, new Arm(site, arm, "", passable.contains(site)));
        }
    }

    private static void deciders(Map<String, Arm> table,
                                 List<StaticScopeMap.Guard> deciders,
                                 boolean wanted) {
        Map<String, StaticScopeMap.Guard> chosen =
                new LinkedHashMap<String, StaticScopeMap.Guard>();
        Map<String, Set<Boolean>> leaving =
                new LinkedHashMap<String, Set<Boolean>>();
        Map<String, Set<Boolean>> arms =
                new LinkedHashMap<String, Set<Boolean>>();
        for (StaticScopeMap.Guard decider : deciders) {
            if (decider.outcome() == null) continue;
            arms.computeIfAbsent(decider.siteId(),
                    site -> new HashSet<Boolean>())
                    .add(decider.outcome());
            if (decider.verdict() != null
                    && decider.verdict().booleanValue() != wanted) {
                leaving.computeIfAbsent(decider.siteId(),
                        site -> new HashSet<Boolean>())
                        .add(decider.outcome());
            }
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
            table.put(decider.siteId(), new Arm(decider.siteId(),
                    decider.outcome(), decider.via(),
                    arms.get(decider.siteId()).size() == 2
                            && !leaving.containsKey(decider.siteId())));
            deciders(table, decider.deciders(), decider.outcome());
        }
    }

    public static Map<String, Arm> read(JsonElement json) {
        Map<String, Arm> table = new LinkedHashMap<String, Arm>();
        if (json == null || !json.isJsonArray()) return table;
        for (JsonElement element : json.getAsJsonArray()) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String site = optionalString(row, "siteId");
            if (site.isEmpty() || table.containsKey(site)
                    || !row.has("arm")) {
                continue;
            }
            table.put(site, new Arm(site, row.get("arm").getAsBoolean(),
                    optionalString(row, "via"),
                    row.has(PASSABLE) && row.get(PASSABLE).getAsBoolean()));
        }
        return Collections.unmodifiableMap(table);
    }

    public static JsonArray forOccurrence(JsonArray table, Set<String> throwMethods,
                                          Set<String> observed) {
        boolean entered = false;
        for (String site : observed) {
            entered |= throwMethods.contains(SiteId.methodOf(site));
        }
        if (!entered) return table.deepCopy();
        JsonArray kept = new JsonArray();
        for (JsonElement row : table) {
            if (!row.isJsonObject()) continue;
            JsonObject arm = row.getAsJsonObject();
            if (arm.has("via") || throwMethods.contains(
                    SiteId.methodOf(optionalString(arm, "siteId")))) {
                kept.add(arm.deepCopy());
            }
        }
        return kept;
    }
}
