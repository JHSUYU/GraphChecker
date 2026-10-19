package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

public final class Moved {
    final Map<String, String> values = new LinkedHashMap<String, String>();
    final Map<String, String> skews = new LinkedHashMap<String, String>();
    final Map<String, String> mints = new LinkedHashMap<String, String>();
    final Set<String> anchored = new LinkedHashSet<String>();
    final Map<String, String> recorded = new LinkedHashMap<String, String>();
    String refusal = "";

    private Moved() {
    }

    public static Moved of(Map<String, String> movedRoots,
                           Map<String, String> readings,
                           SessionReader session, SessionReader recording) {
        Moved moved = new Moved();
        moved.anchored.addAll(readings.keySet());
        Map<String, RootMintRow> named =
                new LinkedHashMap<String, RootMintRow>();
        Map<String, RootMintRow> minted =
                new LinkedHashMap<String, RootMintRow>();
        for (SessionReader rows : Arrays.asList(recording, session)) {
            for (RootMintRow row : rows.roots()) {
                named.putIfAbsent(row.rootId(), row);
                named.putIfAbsent(row.symbol(), row);
                if (rows == recording) {
                    minted.putIfAbsent(row.rootId(), row);
                    moved.recorded.putIfAbsent(row.rootId(),
                            row.recordedValue());
                }
            }
        }
        for (Map.Entry<String, String> entry : movedRoots.entrySet()) {
            RootMintRow row = named.get(entry.getKey());
            RootMintRow mint = row == null ? null : minted.get(row.rootId());
            if (mint == null) {
                moved.refuse("the claim moves " + entry.getKey()
                        + ", which the recording mints nowhere, so no "
                        + "occurrence of a replay can be focused to plant it");
                continue;
            }
            String model = entry.getValue().trim();
            if (row.kind() == RootKind.CLOCK) {
                String skew = ObligationFactory.skew(model,
                        readings.get(row.rootId()));
                if (skew.isEmpty()) {
                    moved.refuse("the model moves clock cell "
                            + entry.getKey() + " to " + model + " and the "
                            + "composition anchors no reading of it, so no "
                            + "skew states that instant");
                    continue;
                }
                moved.skews.put(row.rootId(), skew);
            } else {
                moved.values.put(row.rootId(), model);
            }
            moved.mints.put(row.rootId(), mint.occurrence().render());
        }
        return moved;
    }

    private void refuse(String why) {
        if (refusal.isEmpty()) refusal = why;
    }

    void plant(Map<String, String> assignments,
               Map<String, String> clockDeltas,
               Map<String, String> mints) {
        if (!refusal.isEmpty()) throw new ConfirmMain.Refused(refusal);
        clockDeltas.keySet().removeAll(anchored);
        clockDeltas.putAll(skews);
        assignments.putAll(values);
        mints.putAll(this.mints);
    }

    public boolean ranBy(Corpus.World world, SessionReader session) {
        return ranRootsBy(world, session) && clocksOf(world.clockDeltas);
    }

    public boolean ranRootsBy(Corpus.World world, SessionReader session) {
        return world.pairings.isEmpty() && rootsOf(world, session);
    }

    public boolean ranWorldBy(Corpus.World world, SessionReader session,
                              Set<String> readers) {
        return world.pairings.keySet().equals(readers)
                && rootsOf(world, session) && clocksOf(world.clockDeltas);
    }

    private boolean rootsOf(Corpus.World world, SessionReader session) {
        if (!refusal.isEmpty()) return false;
        for (Map.Entry<String, String> planted
                : world.rootAssignments.entrySet()) {
            if (values.containsKey(planted.getKey())) continue;
            String at = recorded.get(planted.getKey());
            if (at == null || !at.trim().equalsIgnoreCase(
                    planted.getValue().trim())) {
                return false;
            }
        }
        Map<String, String> ran = new LinkedHashMap<String, String>();
        for (RootMintRow row : session.roots()) {
            ran.put(row.rootId(), row.recordedValue());
        }
        for (Map.Entry<String, String> value : values.entrySet()) {
            String at = ran.get(value.getKey());
            if (at == null
                    || !at.trim().equalsIgnoreCase(value.getValue())) {
                return false;
            }
        }
        return true;
    }

    int count() {
        return values.size() + skews.size();
    }

    private boolean clocksOf(Map<String, String> clockDeltas) {
        Map<String, BigInteger> planted =
                new LinkedHashMap<String, BigInteger>();
        for (Map.Entry<String, String> delta : clockDeltas.entrySet()) {
            if (!anchored.contains(delta.getKey())) continue;
            BigInteger skew = number(delta.getValue());
            if (skew == null) return false;
            planted.put(delta.getKey(), skew);
        }
        Map<String, BigInteger> model =
                new LinkedHashMap<String, BigInteger>();
        for (Map.Entry<String, String> skew : skews.entrySet()) {
            model.put(skew.getKey(), number(skew.getValue()));
        }
        return planted.equals(model);
    }

    private static BigInteger number(String text) {
        try {
            return new BigInteger(text.trim());
        } catch (NumberFormatException notANumber) {
            return null;
        }
    }
}
