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
 * there).  A switch guard is not forced (the VM forces an if's arm only),
 * nor a fault call, which no branch decides: a forced world they take
 * elsewhere closes before its target, FORCE_DIVERGED.  A guard each of whose
 * arms reaches the throw within one iteration ({@code
 * StaticScopeMap.Guards#passable}: an {@code assert}'s {@code
 * $assertionsDisabled} test, the first test of {@code if (a || b) throw}),
 * and a decider neither of whose arms leaves the way, are stated {@code
 * passable} and never forced: forcing one against its concrete arm would put
 * {@code false} in the forced condition (that world cannot take it), while
 * either arm leads on to the branches that are forced.  The table is also the one
 * statement of the arm toward the throw COMPOSE asks whether a path left
 * the way at ({@code compose.RestsOn#wayGuard}).  Each TARGET_SITE row has
 * its own table, and a task carries its own target's.</p>
 */
public final class ForcingTable {
    private ForcingTable() {
    }

    /** One if to force, as the VM is asked it
     *  ({@code System.forceNextConcolicBranch(jump)}). */
    public static final class Arm {
        public final String siteId;
        /** Whether it jumps (true) or falls through. */
        public final boolean arm;
        /** The method a decider's helper must be called from, or "". */
        public final String via;
        /** Whether its other arm reaches the throw too: never forced. */
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

    /** SEED: the table of one TARGET_SITE, from its guards, chain and
     *  deciders, the {@code passable} branches among them marked; a site
     *  named twice keeps its first arm. */
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
                deciders(table, deciders, arm, SiteId.methodOf(site));
            }
        }
        for (StaticScopeMap.Guard guard : target.chain) {
            branch(table, guard.siteId(), guard.outcome(), passable);
            if (guard.outcome() != null) {
                deciders(table, guard.deciders(), guard.outcome(),
                        SiteId.methodOf(guard.siteId()));
            }
        }
        JsonArray json = new JsonArray();
        for (Arm forced : table.values()) json.add(forced.toJson());
        return json;
    }

    /** One guard, an if at its arm (a switch states none: not forced). */
    private static void branch(Map<String, Arm> table, String site,
                               Boolean arm, Set<String> passable) {
        if (arm != null && !table.containsKey(site)) {
            table.put(site, new Arm(site, arm, "", passable.contains(site)));
        }
    }

    /**
     * The decider arms of one guard that make it take {@code wanted}: per
     * decider site the arm whose verdict is {@code wanted}, else its open
     * arm; the deciders of the arm chosen, in turn, at that arm.  A decider
     * neither of whose arms leaves the way -- each runs to a return whose
     * verdict is {@code wanted}, or on to a value no constant states (an
     * open arm) -- is {@code passable}, as a guard each of whose arms
     * reaches the throw is: forcing it against its concrete arm would put
     * {@code false} in the forced condition for an arm that leads on too.
     */
    private static void deciders(Map<String, Arm> table,
                                 List<StaticScopeMap.Guard> deciders,
                                 boolean wanted, String via) {
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
                    decider.outcome(), via,
                    arms.get(decider.siteId()).size() == 2
                            && !leaving.containsKey(decider.siteId())));
            deciders(table, decider.deciders(), decider.outcome(),
                    SiteId.methodOf(decider.siteId()));
        }
    }

    /** A table as {@link #of} wrote it, by site, its passable rows
     *  included; a row it cannot read is none. */
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

    /**
     * PLAN: the table one declared occurrence is forced by.  Where the
     * recording's occurrence entered the throw's method (it decided a branch
     * there, {@code observed}), a caller's chain guard is left out: the run
     * reaches the method by some call, and forcing the guard of another call
     * into it would only divert it (solr-18413 FA1: two callers' guards,
     * concrete, forced off the way the recording took into the method, and
     * the forced condition was {@code false}).  The throw's method's own
     * branches and the deciders (forced only in a call from their {@code
     * via}) stay.
     */
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
